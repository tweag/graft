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
-- The explanations here assume you've understood the simple tutorial in
-- "Examples.Ltl.Simple".
module Examples.Ltl.HigherOrder where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer
import Effect.Error
import Effect.Error.Passthrough ()
import Effect.TH
import Logic.Ltl
import Logic.SingleStep

-- * Example domain specification

-- $doc
-- Our domain will be a low level, Turing-complete, abstract machine
-- called 'MonadMiniLang' which is based on a stack of integers and
-- booleans and can raise three different errors. Values can be popped
-- and pushed, arbitrary text can be printed, and two control
-- structures are present: 'if_' and 'while_'.
--
-- These two latter operations are what makes 'MonadMiniLang' a
-- /higher order domain/: There are /nesting/ operations, that is,
-- operations that have sequences of operations in the same monad as
-- parameters.
--
-- In Graft, nested operations must occur in /positive position/ for
-- conceptual and technical reasons. As a reminder, @x@ is in
-- /positive/ position in @t@ if it stands before an even number of
-- @->@s, otherwise it is in /negative/ position. A few examples:
--
-- - In @a -> b@, @a@ is in negative position, @b@ in positive
-- - position.
--
-- - In @(a -> b) -> c@, @a@ and @c@ are in positive position, and @b@
--   is in negative position.
--
-- - In @Maybe ((a -> [b]) -> c) -> d@, @d@ and @b@ are in positive
--   position, and @a@ and @c@ are in negative position.

data MiniLangValue
  = MiniLangInteger Integer
  | MiniLangBoolean Bool
  deriving (Show, Eq)

data MiniLangError
  = StackUnderflow
  | ExpectedBoolean
  | ExpectedInteger
  deriving (Show, Eq)

class (Monad m) => MonadMiniLang m where
  push :: MiniLangValue -> m ()
  pop :: m MiniLangValue
  echo :: String -> m ()
  if_ :: m a -> m a -> m a
  while_ :: m () -> m ()

-- $doc
-- A concrete implementation for our domain: we use
--
-- - a list of values as inner state to account for the stack
--
-- - a writer to allow printing strings using 'echo'
--
-- - an exception to cover possible errors

type MiniLangT m = ExceptT MiniLangError (WriterT String (StateT [MiniLangValue] m))

runMiniLangT :: (Functor m) => MiniLangT m a -> m ((Either MiniLangError a, String), [MiniLangValue])
runMiniLangT m = runStateT (runWriterT (runExceptT m)) []

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

-- $doc
-- As in the simple tutorial, the 'MonadPlus' instance is necessary
-- boilerplate for the interpretation of 'Ltl' formulas, since there
-- might be several ways to satisfy one formula, and we want to try
-- them all.

instance {-# OVERLAPPING #-} (MonadPlus m) => Alternative (MiniLangT m) where
  empty = lift $ lift mzero
  ExceptT (WriterT (StateT f)) <|> ExceptT (WriterT (StateT g)) =
    ExceptT . WriterT . StateT $ \s -> f s `mplus` g s

instance {-# OVERLAPPING #-} (MonadPlus m) => MonadPlus (MiniLangT m)

-- * Using the effect system

-- $doc
-- To obtain the effects associated with "MiniLang" for free, we call
-- the same macros as in "Examples.Ltl.Simple" which also work in
-- higher order settings.

defineEffectType ''MonadMiniLang
makeEffect ''MonadMiniLang ''MonadMiniLangEffect

-- * Example programs in 'MonadMiniLang'

-- | A program that computes the nth Fibonacci number.
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

-- | A program that computes the greatest common divisor of two numbers.
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

-- ** Helper functions used in the example programs

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

-- * Defining single step modifications

-- $doc
-- Our type of modifications is a conjunction of a function to be
-- applied before pushing a value, and a function to be applied after
-- poping a value. To combine those within a Semigroup instance, we
-- compose them while accounting for the fact that they can return
-- 'Nothing'.
--
-- Again, as explained in the simple tutorial, the
-- 'Semigroup' instance is necessary because evaluation of 'Ltl'
-- formulas might sometimes make it necessary to apply more than one
-- modification on the same operation.

data MiniLangMod = MiniLangMod
  { onPop :: MiniLangValue -> Maybe MiniLangValue,
    onPush :: MiniLangValue -> Maybe MiniLangValue
  }

instance Semigroup MiniLangMod where
  MiniLangMod fPop fPush <> MiniLangMod gPop gPush =
    MiniLangMod
      (\x -> (fPop <=< gPop) x <|> fPop x <|> gPop x)
      (\x -> (fPush <=< gPush) x <|> fPush x <|> gPush x)

-- $doc
-- Meaning is given to the single step modifications through their
-- interpretation over our domain. This is what the class
-- 'InterpretLtlHigherOrder' is for. There are two main differences
-- with the first order case:
--
-- - The interpretation function directly handles 'Ltl'
--   formulas. (Remember that the 'InterpretMod' instance in the
--   simple tutorial only has to handle single-step modifications.)
--   This is because the approach based on applying atomic
--   modifications to single operations breaks down for higher-order
--   operations: a single higher-order operation may contain sequences
--   ('AST's) of operations.
--
-- - An explicit distinction needs to be made between first-order and
--   higher-order effect constructors, by using 'Direct' and 'Nested'
--   respectively.
--
-- Considering the second difference:
--
-- - Using 'Direct' signals that the operation at hand is first order,
--   and you can proceed as if writing an 'InterpretMod' instance, as
--   explained in the simple tutorial.
--
-- - Using 'Nested' means the operation is of higher order. This case
--   is detailed below.
--
-- Handling higher order operations:
--
-- In the first order setting, we have the convenient class
-- 'InterpretMod' which allows us to specify how single-step
-- modifications should be applied on operations. In the higher order
-- setting the question is different: applying a single step
-- modification on a nested operation makes no sense because it will
-- likely contain several such operations, thus we provide the whole
-- set of formulas to be applied currently and leave it to the user as
-- to how they should be handling those. While it seems complicated,
-- it is actually pretty straighforward in most cases as the user has
-- sufficient domain knowledge to know how and when the nested blocks
-- will be executed.
--
-- In the example:
--
-- Let's explain 'if_' here. The typical behaviour of 'if_' will be to
-- evaluate the condition and pass the formula that modifies the
-- remainder of the computation to either of the two branches,
-- depending on whether the condition was true or false. In the case
-- of our example, evaluation the condition is itself an operation,
-- namely a 'pop'. So, we will first consume the next single step
-- modification and apply it to that 'pop'. If that was successful,
-- we'll pass on the remaining formulas to the correct block depending
-- on the result of the (possibly modified) result of evaluating the
-- condition.
--
-- Note how we use the function 'nowLaterList' which, from a list of
-- Ltl formulas, creates a list of pairs of a modification to be
-- applied now and the remaining formulas. This function will likely
-- often be called in higher order operations.

instance
  (MonadPlus m, MonadError MiniLangError m, MonadMiniLang m) =>
  InterpretLtlHigherOrder MiniLangMod m MonadMiniLangEffect
  where
  interpretLtlHigherOrder (Push v) = Direct $ Visible $ \modif ->
    case onPush modif v of
      Just v' -> Just <$> push v'
      Nothing -> return Nothing
  interpretLtlHigherOrder Pop = Direct $ Visible $ \modif -> onPop modif <$> pop
  interpretLtlHigherOrder Echo {} = Direct Invisible
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

-- * Smart constructors of modifications

-- | Modify boolean values on pop
popBoolMiniLangMod :: (Bool -> Maybe Bool) -> MiniLangMod
popBoolMiniLangMod f =
  MiniLangMod
    { onPop = \case
        MiniLangBoolean b -> MiniLangBoolean <$> f b
        _ -> Nothing,
      onPush = const Nothing
    }

-- | Modify integer values on pop
popIntegerMiniLangMod :: (Integer -> Maybe Integer) -> MiniLangMod
popIntegerMiniLangMod f =
  MiniLangMod
    { onPop = \case
        MiniLangInteger n -> MiniLangInteger <$> f n
        _ -> Nothing,
      onPush = const Nothing
    }

-- | Modify all values on pop
popMiniLangMod :: (Bool -> Maybe Bool) -> (Integer -> Maybe Integer) -> MiniLangMod
popMiniLangMod fBool fInteger = popBoolMiniLangMod fBool <> popIntegerMiniLangMod fInteger

-- | Modify booleans on push
pushBoolMiniLangMod :: (Bool -> Maybe Bool) -> MiniLangMod
pushBoolMiniLangMod f =
  MiniLangMod
    { onPop = const Nothing,
      onPush = \case
        MiniLangBoolean b -> MiniLangBoolean <$> f b
        _ -> Nothing
    }

-- | Modify integers on push
pushIntegerMiniLangMod :: (Integer -> Maybe Integer) -> MiniLangMod
pushIntegerMiniLangMod f =
  MiniLangMod
    { onPop = const Nothing,
      onPush = \case
        MiniLangInteger n -> MiniLangInteger <$> f n
        _ -> Nothing
    }

-- | Modify all values on push
pushMiniLangMod :: (Bool -> Maybe Bool) -> (Integer -> Maybe Integer) -> MiniLangMod
pushMiniLangMod fBool fInteger = pushBoolMiniLangMod fBool <> pushIntegerMiniLangMod fInteger

-- | Negate booleans on pop and push
flipBools :: MiniLangMod
flipBools = popBoolMiniLangMod (Just . not) <> pushBoolMiniLangMod (Just . not)

-- | Negate integers on pop and push
flipIntegers :: MiniLangMod
flipIntegers = popIntegerMiniLangMod (Just . negate) <> pushIntegerMiniLangMod (Just . negate)

-- | Negate all values on pop and push
flipBoth :: MiniLangMod
flipBoth = flipBools <> flipIntegers

-- | Apply the modulo operation on pop and push for integers
moduloMiniLangMod :: Integer -> MiniLangMod
moduloMiniLangMod n = popIntegerMiniLangMod (Just . (`mod` n)) <> pushIntegerMiniLangMod (Just . (`mod` n))

-- * Running modified MiniLang programs

-- $doc
-- As in the simple tutorial, we can use the function
-- 'interpretLtlAST' to obtain a function that will interpret an
-- 'LtlAST' of 'MonadMiniLangEffect' and 'MonadErrorEffect'.
--
-- Note that the 'LtlInstanceKind' for the 'MonadMiniLangEffect' is
-- 'InterpretLtlHigherOrderTag', since that's the instance that we
-- implemented above: @InterpretLtlHigherOrder MiniLangMod m
-- MonadMiniLangEffect@.
--
-- Again, the 'InterpretEffectStateful' instance for @MonadErrorEffect
-- MiniLangError@ is the \"passthrough\" instance imported from
-- "Effect.Error.Passthtrough", which ignores all modifications: We're
-- only interested in modifying 'MonadMiniLang' operations in the
-- program, not its generic error handling.

interpretAndRunMiniLang ::
  LtlAST MiniLangMod '[MonadMiniLangEffect, MonadErrorEffect MiniLangError] a ->
  [((Either MiniLangError a, String), [MiniLangValue])]
interpretAndRunMiniLang =
  runMiniLangT
    . interpretLtlAST
      @'[ InterpretLtlHigherOrderTag,
          InterpretEffectStatefulTag
        ]

-- $doc
-- As in the simple simple tutorial, we can apply the 'modifyLtl'
-- function to modify the 'MonadMiniLang' operations in the program.

exampleSomewhere :: [((Either MiniLangError Integer, String), [MiniLangValue])]
exampleSomewhere = interpretAndRunMiniLang $
  modifyLtl (somewhere flipIntegers) $ do
    echo "Pushing 42"
    pushInteger 42
    popInteger

-- $doc
-- >>> exampleSomewhere
-- [((Right -42,"Pushing 42"),[]),
--  ((Right -42,"Pushing 42"),[])]

-- $doc
-- Let's look at a more interesting example with a higher-order
-- operation, 'if_'.

exampleIf :: MiniLangMod -> Bool -> [((Either MiniLangError (), String), [MiniLangValue])]
exampleIf modif intOrBool = interpretAndRunMiniLang $
  modifyLtl (somewhere modif) $ do
    pushBoolean intOrBool
    if_
      (pushInteger 42)
      (pushBoolean True)

-- $doc
-- >>> exampleIf flipIntegers True
-- [((Right (),""),[MiniLangInteger (-42)]]
--
-- >>> exampleIf flipIntegers False
-- []
--
-- The two runs above show that we only modify the \"else\" branch of
-- the 'if_' when it is executed: in the second run, no modification
-- is applied, because no push or pop involving an integer happens.
--
-- The next two runs are more involved, because we modify booleans,
-- which are intrinsically very relevant for 'if_'s. Let's mark the
-- places that are potentially modified:
--
-- > do
-- >   pushBoolean intOrBool    -- (1) because we push a boolean
-- >   if_                      -- (2) because 'if_' pushes a boolean
-- >     (pushInteger 42)
-- >     (pushBoolean True)     -- (3) because we push a boolean
--
-- The modality 'somewhere' requires that we either modify the
-- 'pushBoolean' at (1), or modify some later 'push' or 'pop' of a
-- boolean. If 'intOrBool' is initially 'True', that means we have two
-- options:
--
-- - modify at (1), which means that the we'll 'pop' a 'False' at
--   (2). In this scenario, we'll execute the 'else' branch, which
--   will 'push' a 'True' at (3).
--
-- - modify at (2), which also means that we'll 'pop' a 'False' at
--   (2). We'll consequently also execute the execute the 'else'
--   branch, which will 'push' a 'True' at (3).
--
-- Note that we'll never apply a modification at (3), because in both
-- cases, the requirements of 'somewhere' are already satisfied.
--
-- >>> exampleIf flipBools True
-- [((Right (), ""), [MiniLangBoolean True]),
--  ((Right (), ""), [MiniLangBoolean True])]
--
-- For our last run, let's look at the case where 'intOrBool' is
-- 'False'. In that case, the following three scenarios are possible:
--
-- - modify at (1), which means that we'll 'pop' a 'True' at (2). So,
--   we'll execute the 'then' branch, which will 'push' a '42'.
--
-- - modify at (2), which means that we'll 'pop' a 'True' at (2). So,
--   we'll execute the 'then' branch, which will 'push' a '42'.
--
-- - If we don't modify at (1) or (2), we'll execute the 'else'
--   branch, which will 'push' a 'False' (modified from 'True') at
--   (3).
--
-- >>> exampleIf flipBools False
-- [((Right (),""),[MiniLangInteger 42]),
--  ((Right (),""),[MiniLangInteger 42]),
--  ((Right (),""),[MiniLangBoolean False])]

-- $doc
-- Finally, for a more testing-flavoured example, we can check the
-- property that the programs only interact with the stack through the
-- 'push' and 'pop' operations, by applying @everywhere
-- flipBoth@. Effectively, this modification means that the entries on
-- the stack will always be the inverse of their "actual" values, and
-- that the meaning of 'push' and 'pop' also contains reversing this
-- polarity.

exampleFlipFibonacci :: Bool
exampleFlipFibonacci =
  all
    ( \n ->
        fmap
          getResult
          ( interpretAndRunMiniLang
              (modifyLtl (everywhere flipBoth) (fibonacciExample n))
          )
          == [getResult . runIdentity $ runMiniLangT (fibonacciExample n)]
    )
    [0 .. 10]
  where
    getResult :: ((Either MiniLangError Integer, String), [MiniLangValue]) -> Either MiniLangError Integer
    getResult = fst . fst

-- $doc
-- >>> exampleFlipFibonacci
-- True
