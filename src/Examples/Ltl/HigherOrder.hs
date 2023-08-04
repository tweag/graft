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

-- | This module contains a more advanced use case for the LTL framework from
-- "Logic.Ltl". It assumes you've read the first tutorial in
-- "Examples.Ltl.Simple".
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
import Language.Haskell.TH (varT)
import Logic.Ltl

-- $doc
-- The idea in this tutorial is to use the key-value store from
-- "Examples.Ltl.Simple" as a basis for a minimal programming language: the
-- keys will be variable names, and the values, well, the values. We add a
-- branching construct 'ifThenElse' and a looping construct 'while'. Both of
-- these have as their first argument a key (i.e. a variable name), and branch
-- depending on whether the value associated to the key is 'truthy'.

type MiniLangError = String

class Truthy v where
  truthy :: v -> Bool

class (Truthy v, MonadKeyValue k v m) => MonadMiniLang k v m where
  ifThenElse :: k -> m a -> m a -> m a
  while :: k -> m () -> m ()

-- $doc
-- As in the first-order tutorial, we also  ave a simple implementation of our
-- interface of interest, @MonadMiniLang@. Note that the branching in the
-- implementation of 'ifThenElse' and 'while' is implemented in a way that is
-- sometimes seen in real-world programming languages (Lua is an example): if
-- there's no value associated to the variable name, that counts as "false"
-- i.e. not 'truthy'.

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
      Nothing -> r
      Just b -> if truthy @v b then l else r
  while test acts = do
    mTest <- getValue test
    case mTest of
      Nothing -> return ()
      Just b ->
        when (truthy @v b) $ acts >> while @k @v test acts

-- TODO after merging PR#2: replace the following up to (***) with
--
-- > defineEffectType ''MonadMiniLang
-- > makeEffect ''MonadMiniLang ''MonadMiniLangEffect
--
-- and reference the explanation in the first tutorial
--

data MiniLangEffect k v :: Effect where
  IfThenElse :: k -> m a -> m a -> MiniLangEffect k v m a
  While :: k -> m () -> MiniLangEffect k v m ()

makeReification
  ( \[k, v] ops ->
      [t|
        ( Truthy $(varT v),
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

-- (***)

-- $doc
-- For our little programming language, let's have booleans and integers, and
-- define them to be 'truthy' in the customary way: booleans truthy by their
-- very nature, integers are truthy if they're nonzero.

data MiniLangValue = MLBool Bool | MLInteger Integer deriving (Show)

instance Truthy MiniLangValue where
  truthy (MLBool b) = b
  truthy (MLInteger i) = i /= 0

-- $doc
-- This next instance is what this tutorial is about. It makes the evaluation
-- of 'Ltl' formulas pass into the two higher-order effects 'IfThenElse' and
-- 'While' in the obvious ways:
--
-- - For 'IfThenElse', look at the condition. If it is 'truthy', continue
--   evaluating the 'Ltl' formula(s) on the "then" branch, otherwise the "else"
--   branch.
--
-- - For 'While', look at the condition. If it is 'truthy', run throuhg the
--   body once more, while continuing to evaluate the 'Ltl' formula(s), otherwise
--   continue evaluation after with whatever remains of the 'Ltl' formula(s).
--
-- TODO: explain it really thoroughly.

instance (MonadMiniLang String MiniLangValue m) => InterpretLtlHigherOrder x m (MiniLangEffect String MiniLangValue) where
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

-- $doc
-- TODO: here are a few silly example programs.

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

-- $doc
-- TODO here is a tweak that will apply a "renaming" function to all variable
-- names. We can use it to "detect" the "strange" behaviour that programs are
-- not invariant under uniform renaming of all variables, because 'ifThenElse'
-- and 'while' use hard-coded variable names.

data Tweak k = Rename (k -> Maybe k)

instance Semigroup (Tweak k) where
  Rename f <> Rename g = Rename $ \key -> (f =<< g key) <|> g key <|> f key

instance (MonadKeyValue k v m) => InterpretLtl (Tweak k) m (KeyValueEffect k v) where
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
    '[ ErrorEffect MiniLangError,
       KeyValueEffect String MiniLangValue,
       MiniLangEffect String MiniLangValue
     ]
    a ->
  [(Either MiniLangError a, Map String MiniLangValue)]
interpretAndRunMiniLang initialState acts =
  runMiniLangT initialState $
    interpretLtlAST
      @'[InterpretEffectStatefulTag, InterpretLtlTag, InterpretLtlHigherOrderTag]
      acts
