{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Examples.Ltl.HigherOrder where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity (Identity (runIdentity))
import Data.Map (Map)
import Effect
import Effect.Error
import Effect.TH
import Examples.Ltl.Simple
import Language.Haskell.TH (varT)
import Logic.Ltl

class Truthy v where
  truthy :: v -> Bool

class (Truthy v, MonadKeyValue k v m, MonadError e m) => MonadMiniLang e k v m where
  ifThenElse :: k -> m a -> m a -> m a
  while :: k -> m () -> m ()

type MiniLangT e k v m = ExceptT e (KeyValueT k v m)

type MiniLang e k v = MiniLangT e k v Identity

runMiniLangT :: Map k v -> MiniLangT e k v m a -> m (Either e a, Map k v)
runMiniLangT initState = runKeyValueT initState . runExceptT

runMiniLang :: Map k v -> MiniLang e k v a -> (Either e a, Map k v)
runMiniLang initState = runIdentity . runMiniLangT initState

instance (Ord k, Monad m) => MonadKeyValue k v (MiniLangT e k v m) where
  storeValue k v = lift $ storeValue k v
  getValue = lift . getValue
  deleteValue = lift . deleteValue @k @v

instance
  (Ord k, Show k, Truthy v, Monad m) =>
  MonadMiniLang String k v (MiniLangT String k v m)
  where
  ifThenElse cond l r = do
    mTest <- getValue cond
    case mTest of
      Nothing -> r -- throwError $ "ifThenElse: unbound variable: " ++ show cond
      Just b -> if truthy @v b then l else r
  while test acts = do
    mTest <- getValue test
    case mTest of
      Nothing -> return () --  throwError $ "while: unbound variable: " ++ show test
      Just b ->
        when (truthy @v b) $ acts >> while @String @k @v test acts

data MiniLangEffect e k v :: Effect where
  IfThenElse :: k -> m a -> m a -> MiniLangEffect e k v m a
  While :: k -> m () -> MiniLangEffect e k v m ()

-- TODO make the error message nicer when we forget constraints on ops

makeReification
  ( \[e, k, v] ops ->
      [t|
        ( Truthy $(varT v),
          EffectInject (ErrorEffect $(varT e)) $(varT ops),
          EffectInject (KeyValueEffect $(varT k) $(varT v)) $(varT ops)
        )
        |]
  )
  ''MonadMiniLang
  ''MiniLangEffect

makeInterpretation
  (\_ _ -> [t|()|])
  ''MonadMiniLang
  ''MiniLangEffect

data MiniLangValue = MLBool Bool | MLInteger Integer deriving (Show)

instance Truthy MiniLangValue where
  truthy (MLBool b) = b
  truthy (MLInteger i) = i /= 0

-- instance (MonadMiniLang String String MiniLangValue m) => InterpretLtlHigherOrder x m (MiniLangEffect String String MiniLangValue) where
--  interpretLtlHigherOrder (IfThenElse cond l r) = Nested $
--    \evalAST ltls -> do
--      ifThenElse @String @String @MiniLangValue
--        cond
--        (evalAST ltls l)
--        (evalAST ltls r)
--  interpretLtlHigherOrder (While cond body) = Nested $
--    \evalAST ltls -> whileWithLtls evalAST ltls cond body
--    where
--      whileWithLtls evalAST ltls test acts = do
--        mTest <- getValue test
--        case truthy <$> mTest of
--          Nothing -> throwError $ "while: unbound variable: " ++ test
--          Just b -> do
--            if b
--              then do
--                (_, ltls') <- evalAST ltls acts
--                whileWithLtls evalAST ltls' test acts
--              else return ((), ltls)
--
--

getInteger :: (MonadMiniLang String String MiniLangValue m) => String -> m Integer
getInteger name = do
  mi <- getValue name
  case mi of
    Just (MLInteger i) -> return i
    Just _ -> throwError $ "not an Integer: " ++ name
    Nothing -> throwError $ "unbond variable: " ++ name

fibonacciTest :: (MonadMiniLang String String MiniLangValue m) => Integer -> m Integer
fibonacciTest n = do
  storeValue "n" $ MLInteger n
  storeValue "a" $ MLInteger 0
  storeValue "b" $ MLInteger 1
  while @_ @_ @MiniLangValue "n" $ do
    n <- getInteger "n"
    a <- getInteger "a"
    b <- getInteger "b"
    storeValue "b" $ MLInteger (a + b)
    storeValue "a" $ MLInteger b
    storeValue "n" $ MLInteger (n - 1)
  getInteger "a"

branchTest :: (MonadMiniLang String String MiniLangValue m) => Integer -> m Integer
branchTest n = do
  storeValue "n" $ MLInteger n
  ifThenElse @_ @_ @MiniLangValue "n" (return 3) (return 4)

simpleRun :: (Ord k) => MiniLangT String k v Identity a -> (Either String a, Map k v)
simpleRun = runMiniLang mempty

foo :: Integer -> (Either String Integer, Map String MiniLangValue)
foo = simpleRun . fibonacciTest

bar :: Integer -> (Either String Integer, Map String MiniLangValue)
bar = simpleRun . branchTest
