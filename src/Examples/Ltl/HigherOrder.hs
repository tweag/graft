{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Examples.Ltl.HigherOrder where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity (Identity (runIdentity))
import Data.Map (Map)
import Effect
import Effect.Error
import Effect.Error.Passthrough ()
import Effect.TH
import Examples.Ltl.Simple
import Logic.Ltl

type MiniLangError = String

class Truthy v where
  truthy :: v -> Bool

class (Truthy v, MonadKeyValue k v m) => MonadMiniLang k v m where
  ifThenElse :: k -> m a -> m a -> m a
  while :: k -> m () -> m ()

type MiniLangT k v m = ExceptT MiniLangError (KeyValueT k v m)

type MiniLang k v = MiniLangT k v Identity

runMiniLangT :: Map k v -> MiniLangT k v m a -> m (Either MiniLangError a, Map k v)
runMiniLangT initState = runKeyValueT initState . runExceptT

runMiniLang :: Map k v -> MiniLang k v a -> (Either MiniLangError a, Map k v)
runMiniLang initState = runIdentity . runMiniLangT initState

instance (Ord k, Monad m) => MonadKeyValue k v (MiniLangT k v m) where
  storeValue k v = lift $ storeValue k v
  getValue = lift . getValue
  deleteValue = lift . deleteValue @k @v

instance
  (Ord k, Show k, Truthy v, Monad m) =>
  MonadMiniLang k v (MiniLangT k v m)
  where
  ifThenElse cond l r = do
    mTest <- getValue cond
    case mTest of
      Nothing -> r -- throwError
      Just b -> if truthy @v b then l else r
  while test acts = do
    mTest <- getValue test
    case mTest of
      Nothing -> return ()
      Just b ->
        when (truthy @v b) $ acts >> while @k @v test acts

data MonadMiniLangEffect k v :: Effect where
  IfThenElse :: k -> m a -> m a -> MonadMiniLangEffect k v m a
  While :: k -> m () -> MonadMiniLangEffect k v m ()

-- TODO make the error message nicer when we forget constraints on ops

makeEffect ''MonadMiniLang ''MonadMiniLangEffect

data MiniLangValue = MLBool Bool | MLInteger Integer deriving (Show)

instance Truthy MiniLangValue where
  truthy (MLBool b) = b
  truthy (MLInteger i) = i /= 0

instance (MonadMiniLang String MiniLangValue m) => InterpretLtlHigherOrder x m (MonadMiniLangEffect String MiniLangValue) where
  interpretLtlHigherOrder (IfThenElse cond l r) = Nested $
    \evalAST ltls -> do
      ifThenElse @String @MiniLangValue
        cond
        (evalAST ltls l)
        (evalAST ltls r)
  interpretLtlHigherOrder (While cond body) = Nested $
    \evalAST ltls -> whileWithLtls evalAST ltls cond body
    where
      whileWithLtls ::
        (MonadMiniLang String MiniLangValue m) =>
        ([Ltl mod] -> AST ops () -> m ((), [Ltl mod])) ->
        [Ltl mod] ->
        String ->
        AST ops () ->
        m ((), [Ltl mod])
      whileWithLtls evalAST ltls test acts = do
        mTest <- getValue test
        case truthy @MiniLangValue <$> mTest of
          Nothing -> return ((), ltls)
          Just b -> do
            if b
              then do
                (_, ltls') <- evalAST ltls acts
                whileWithLtls evalAST ltls' test acts
              else return ((), ltls)

getInteger :: (MonadError MiniLangError m, MonadMiniLang String MiniLangValue m) => String -> m Integer
getInteger name = do
  mi <- getValue name
  case mi of
    Just (MLInteger i) -> return i
    Just _ -> throwError $ "not an Integer: " ++ name
    Nothing -> throwError $ "unbond variable: " ++ name

fibonacciTest :: (MonadError MiniLangError m, MonadMiniLang String MiniLangValue m) => Integer -> m Integer
fibonacciTest n = do
  storeValue "n" $ MLInteger n
  storeValue "a" $ MLInteger 0
  storeValue "b" $ MLInteger 1
  while @_ @MiniLangValue "n" $ do
    n <- getInteger "n"
    a <- getInteger "a"
    b <- getInteger "b"
    storeValue "b" $ MLInteger (a + b)
    storeValue "a" $ MLInteger b
    storeValue "n" $ MLInteger (n - 1)
  getInteger "a"

branchTest :: (MonadMiniLang String MiniLangValue m) => Integer -> m Integer
branchTest n = do
  storeValue "n" $ MLInteger n
  ifThenElse @_ @MiniLangValue "n" (return 3) (return 4)

simpleRun :: (Ord k) => MiniLangT k v Identity a -> (Either String a, Map k v)
simpleRun = runMiniLang mempty

foo :: Integer -> (Either String Integer, Map String MiniLangValue)
foo = simpleRun . fibonacciTest

bar :: Integer -> (Either String Integer, Map String MiniLangValue)
bar = simpleRun . branchTest

data Tweak k = Rename (k -> Maybe k)

instance Semigroup (Tweak k) where
  Rename f <> Rename g = Rename $ \key -> (f =<< g key) <|> g key <|> f key

instance (MonadKeyValue k v m) => InterpretLtl (Tweak k) m (MonadKeyValueEffect k v) where
  interpretLtl (GetValue key) = Apply $ \(Rename f) -> case f key of
    Nothing -> return Nothing
    Just key' -> Just <$> getValue key'
  interpretLtl (StoreValue key val) = Apply $ \(Rename f) -> case f key of
    Nothing -> return Nothing
    Just key' -> storeValue key' val >> return (Just ())
  interpretLtl (DeleteValue key) = Apply $ \(Rename f) -> case f key of
    Nothing -> return Nothing
    Just key' -> deleteValue @_ @v key' >> return (Just ())

interpretAndRunMiniLang ::
  Map String MiniLangValue ->
  LtlAST
    (Tweak String)
    '[ MonadErrorEffect MiniLangError,
       MonadKeyValueEffect String MiniLangValue,
       MonadMiniLangEffect String MiniLangValue
     ]
    a ->
  [(Either MiniLangError a, Map String MiniLangValue)]
interpretAndRunMiniLang initialState acts =
  runMiniLangT initialState $
    interpretLtlAST
      @'[InterpretEffectStatefulTag, InterpretLtlTag, InterpretLtlHigherOrderTag]
      acts
