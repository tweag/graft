{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

-- | A tutorial for how to use "Logic.Ltl" with higher-order effects.
-- Understanding of "Simple.hs" for first order effects is assumed and
-- elements revolving around higher order constructors only will be
-- further detailed alongside domain explanations.
module Examples.Ltl.HigherOrderAlternative where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Effect.Error
import Effect.Error.Passthrough ()
import Effect.TH
import Logic.Ltl
import Logic.SingleStep

-- * Example domain specification

-- $doc 
-- Our domain will be a low level, turing-complete, abstract machine
-- called 'MonadMiniLang' which works on integers and booleans and can
-- raise a set of three errors. Values can be popped and pushed,
-- arbitrary text can be printed, and two control structures are
-- present: 'if_' and 'while_'.
--
-- These two latter operations are what makes 'MonadMiniLang' a /higher order domain/: 
-- Such domains have /nested operations/, that
-- is, operations that have sequences of operations as parameters. These seqences of operations must occur in
-- positive positions (e.g. `(x -> m a) -> m a)` is forbidden but `(m a ->
-- x) -> m a` is allowed).
--

data MiniLangValue
  = MiniLangInteger Integer
  | MiniLangBoolean Bool
  deriving (Show)

data MiniLangError
  = StackUnderflow
  | ExpectedBoolean
  | ExpectedInteger
  deriving (Show)

class (Monad m) => MonadMiniLang m where
  push :: MiniLangValue -> m ()
  pop :: m MiniLangValue
  echo :: String -> m ()
  if_ :: m a -> m a -> m a
  while_ :: m () -> m ()

-- $doc A concrete implementation for our domain: we use
--
-- - a list of values as inner state to account for the stack
-- - a writer to allow printing strings using 'echo'
-- - an exception to cover possible errors

type MiniLangT m = ExceptT MiniLangError (WriterT String (StateT [MiniLangValue] m))


-- $doc
-- The 'MonadPlus' instance will be necessary later on for the interpretation of 'Ltl' formulas, since there might be several ways to satisfy one formula, and we want to try them all.

instance {-# OVERLAPPING #-} (MonadPlus m) => Alternative (MiniLangT m) where
  empty = lift $ lift mzero
  ExceptT (WriterT (StateT f)) <|> ExceptT (WriterT (StateT g)) =
    ExceptT . WriterT . StateT $ \s -> f s `mplus` g s

instance {-# OVERLAPPING #-} (MonadPlus m) => MonadPlus (MiniLangT m)

instance (Monad m) => MonadMiniLang (MiniLangT m) where
  push v = do
    vs <- get
    put (v : vs)
  pop = do
    vs <- get
    case vs of
      [] -> throwError StackUnderflow
      (v : vs') -> put vs' >> return v
  echo = tell
  if_ m1 m2 = do
    v <- pop
    case v of
      MiniLangBoolean True -> m1
      MiniLangBoolean False -> m2
      _ -> throwError ExpectedBoolean
  while_ m = do
    v <- pop
    case v of
      MiniLangBoolean True -> m >> while_ m
      MiniLangBoolean False -> return ()
      _ -> throwError ExpectedBoolean

runMiniLangT :: (Functor m) => MiniLangT m a -> m ((Either MiniLangError a, String), [MiniLangValue])
runMiniLangT m = runStateT (runWriterT (runExceptT m)) []

-- * Using the effect system

-- $doc To obtain the effects associated with "MiniLang" for free, we
-- call the two following macros. They work as explained in "Examples.Ltl.Simple"; the higher-order operations don't change that. 

defineEffectType ''MonadMiniLang
makeEffect ''MonadMiniLang ''MonadMiniLangEffect

-- * Defining single step modifications

-- $doc Our type of modifications is a conjunction of a function to be
-- applied before pushing a value, and a function to be applied after
-- poping a value. To combine those within a Semigroup instance, we
-- compose them while accounting for the fact that they can return
-- 'Nothing'. Again, as explained in the simple tutorial, the 'Semigroup' instance is necessary because evaluation of 'Ltl' formulas might sometimes make it necessary to apply two modifications to the same operation.

data MiniLangMod = MiniLangMod
  { onPop :: MiniLangValue -> Maybe MiniLangValue,
    onPush :: MiniLangValue -> Maybe MiniLangValue
  }

instance Semigroup MiniLangMod where
  MiniLangMod fPop fPush <> MiniLangMod gPop gPush =
    MiniLangMod
      (\x -> (fPop <=< gPop) x <|> fPop x <|> gPop x)
      (\x -> (fPush <=< gPush) x <|> fPush x <|> gPush x)

-- $doc A meaning is given to the single step modifications through
-- their interpretation over our domain. This is what the class 'InterpretLtlHigherOrder' is for. There are two main
-- differences with the first order case:
--
-- - The interpretation function is directly dependant on Ltl (hence
--   the name 'InterpretLtlHigherOrder') as the Ltl formula needs to
--   be passed down explicitly in high order constructors
--
-- - An explicit distinction needs to be made between first order and
--   high order constructors, by using 'Direct' and 'Nested'
--   respectively.
--
-- Considering the second difference:
--
-- - Using 'Direct' means the operation at hand is first order and
--   should be treated as such within this constructor.
--
-- - Using 'Nested' means the operation is of higher order. This case
--   is significantly more complicated as it requires to handle Ltl
--   formulas by hand. Achieving this is detailed below.
--
-- Handling higher order operations:
--
-- When using the Ltl logic within the first order setting, it is
-- possible to automatically decide what single step modifications
-- should be applied now and what should be the remaining formulas to
-- be applied later on. While the user can decide what to do with the
-- modification at hand within a given time step (attempting to apply
-- it, ignoring it or passing it on) they do not have to manually pass
-- formulas around. In the higher order setting the question is
-- different: applying a single step modification on a nested
-- operation makes no sense because it will likely contain several
-- such operations, thus we provide the whole set of formulas to be
-- applied currently and leave it to the user as to how they should be
-- handling those. While it seems complicated, it is actually pretty
-- straighforward in most cases as the user has sufficient domain
-- knowledge to know how and when the nested blocks will be executed.
--
-- In the example:
--
-- As an example, the typical behaviour to handle an 'if' will be to
-- evaluate the condition and pass the formula to either side
-- depending on the result of this evalutation. In the case of our
-- example, the condition evaluation is itself an operation (a pop) so
-- it will first consume one of the single step modification, and pass
-- on the remaining of the formula to the right block depending on the
-- result of the evaluation. This passing is done through the use of
-- the 'evalAST' parameter of the function to be defined, while the
-- second parameter, 'ltls' is the set of Ltl formulas to be applied
-- from this point onward. This process uses the function
-- 'nowLaterList' which, from a list of Ltl formulas, creates a list
-- of pairs of modification to be applied now and the remaining
-- formulas. This function will likely often be called in higher order
-- operations.

instance (MonadPlus m, MonadError MiniLangError m, MonadMiniLang m) => InterpretLtlHigherOrder MiniLangMod m MonadMiniLangEffect where
  interpretLtlHigherOrder (Push v) = Direct $ \case
    Just x -> Apply $
      case onPush x v of
        Just v' -> Just <$> push v'
        Nothing -> return Nothing
    Nothing -> DontApply
  interpretLtlHigherOrder Pop = Direct $ \case
    Just x -> Apply $ do
      v <- pop
      case onPop x v of
        Just v' -> return $ Just v'
        Nothing -> return Nothing
    Nothing -> DontApply
  interpretLtlHigherOrder Echo {} = Direct $ const Ignore
  interpretLtlHigherOrder (If_ m1 m2) = Nested $ \evalAST ltls -> do
    v <- pop
    msum $
      map
        ( \(now, later) ->
            let vMiniLangModed = case now of
                  Just x -> onPop x v
                  Nothing -> Just v
             in case vMiniLangModed of
                  Just (MiniLangBoolean True) -> Just <$> evalAST later m1
                  Just (MiniLangBoolean False) -> Just <$> evalAST later m2
                  Nothing -> return Nothing
                  _ -> throwError ExpectedBoolean
        )
        (nowLaterList ltls)
  interpretLtlHigherOrder (While_ m) = Nested $ \evalAST ltls -> do
    v <- pop
    msum $
      map
        ( \(now, later) ->
            let vMiniLangModed = case now of
                  Just x -> onPop x v
                  Nothing -> Just v
             in case vMiniLangModed of
                  Just (MiniLangBoolean True) -> do
                    ((), later') <- evalAST later m
                    case interpretLtlHigherOrder (While_ m) of
                      Nested f -> f evalAST later'
                      _ -> error "impossible"
                  Just (MiniLangBoolean False) -> return $ Just ((), later)
                  Nothing -> return Nothing
                  _ -> throwError ExpectedBoolean
        )
        (nowLaterList ltls)

interpretAndRunMiniLang ::
  LtlAST MiniLangMod '[MonadMiniLangEffect, MonadErrorEffect MiniLangError] a ->
  [((Either MiniLangError a, String), [MiniLangValue])]
interpretAndRunMiniLang = runMiniLangT . interpretLtlAST @'[InterpretLtlHigherOrderTag, InterpretEffectStatefulTag]

-- * Helper function to push and pop specific kinds of values

popInteger :: (MonadError MiniLangError m, MonadMiniLang m) => m Integer
popInteger =
  pop >>= \case
    MiniLangInteger n -> return n
    _ -> throwError ExpectedInteger

pushInteger :: (MonadMiniLang m) => Integer -> m ()
pushInteger = push . MiniLangInteger

popBoolean :: (MonadError MiniLangError m, MonadMiniLang m) => m Bool
popBoolean =
  pop >>= \case
    MiniLangBoolean b -> return b
    _ -> throwError ExpectedBoolean

pushBoolean :: (MonadMiniLang m) => Bool -> m ()
pushBoolean = push . MiniLangBoolean

-- * Examples of programs using MiniLang. Fibonacci and gcd.

fibonacciExample :: (MonadError MiniLangError m, MonadMiniLang m) => Integer -> m Integer
fibonacciExample n = do
  pushInteger 1
  pushInteger 0
  pushInteger n
  pushBoolean (n > 0)
  while_ $ do
    n' <- popInteger
    b <- popInteger
    a <- popInteger
    echo $ show n' ++ ", " ++ show a ++ ", " ++ show b ++ "\n"
    pushInteger (a + b)
    pushInteger a
    pushInteger (n' - 1)
    pushBoolean (n' > 1)
  _ <- popInteger
  popInteger

gcdExample :: (MonadError MiniLangError m, MonadMiniLang m) => Integer -> Integer -> m Integer
gcdExample a b = do
  pushInteger a
  pushInteger b
  pushBoolean (0 /= b)
  while_ $ do
    b' <- popInteger
    a' <- popInteger
    pushInteger b'
    pushInteger (a' `mod` b')
    pushBoolean (0 /= a' `mod` b')
  _ <- popInteger
  popInteger

-- * Examples of modifications:

-- $doc Modifies boolean values on pop

popBoolMiniLangMod :: (Bool -> Maybe Bool) -> MiniLangMod
popBoolMiniLangMod f =
  MiniLangMod
    { onPop = \case
        MiniLangBoolean b -> MiniLangBoolean <$> f b
        _ -> Nothing,
      onPush = const Nothing
    }

-- $doc Modifies integer values on pop

popIntegerMiniLangMod :: (Integer -> Maybe Integer) -> MiniLangMod
popIntegerMiniLangMod f =
  MiniLangMod
    { onPop = \case
        MiniLangInteger n -> MiniLangInteger <$> f n
        _ -> Nothing,
      onPush = const Nothing
    }

-- $doc Modifies all values on pop

popMiniLangMod :: (Bool -> Maybe Bool) -> (Integer -> Maybe Integer) -> MiniLangMod
popMiniLangMod fBool fInteger = popBoolMiniLangMod fBool <> popIntegerMiniLangMod fInteger

-- $doc Modifies booleans on push

pushBoolMiniLangMod :: (Bool -> Maybe Bool) -> MiniLangMod
pushBoolMiniLangMod f =
  MiniLangMod
    { onPop = const Nothing,
      onPush = \case
        MiniLangBoolean b -> MiniLangBoolean <$> f b
        _ -> Nothing
    }

-- $doc Modifies integers on push

pushIntegerMiniLangMod :: (Integer -> Maybe Integer) -> MiniLangMod
pushIntegerMiniLangMod f =
  MiniLangMod
    { onPop = const Nothing,
      onPush = \case
        MiniLangInteger n -> MiniLangInteger <$> f n
        _ -> Nothing
    }

-- $doc Modifies all values on push

pushMiniLangMod :: (Bool -> Maybe Bool) -> (Integer -> Maybe Integer) -> MiniLangMod
pushMiniLangMod fBool fInteger = pushBoolMiniLangMod fBool <> pushIntegerMiniLangMod fInteger

-- $doc Negates booleans on pop and push

flipBools :: MiniLangMod
flipBools = popBoolMiniLangMod (Just . not) <> pushBoolMiniLangMod (Just . not)

-- $doc Negates integers on pop and push

flipIntegers :: MiniLangMod
flipIntegers = popIntegerMiniLangMod f <> pushIntegerMiniLangMod f
  where
    f 0 = Nothing
    f n = Just $ negate n

-- $doc Negates all values on pop and push

flipBoth :: MiniLangMod
flipBoth = flipBools <> flipIntegers

-- $doc Applies the modulo operation on pop and push for integers

moduloMiniLangMod :: Integer -> MiniLangMod
moduloMiniLangMod n = popIntegerMiniLangMod (Just . (`mod` n)) <> pushIntegerMiniLangMod (Just . (`mod` n))
