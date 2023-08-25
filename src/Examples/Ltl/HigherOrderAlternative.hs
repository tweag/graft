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

data MiniLangValue = MiniLangInteger Integer | MiniLangBoolean Bool deriving (Show)

data MiniLangError = StackUnderflow | ExpectedBoolean | ExpectedInteger deriving (Show)

class (Monad m) => MonadMiniLang m where
  push :: MiniLangValue -> m ()
  pop :: m MiniLangValue
  echo :: String -> m ()
  if_ :: m a -> m a -> m a
  while_ :: m () -> m ()

defineEffectType ''MonadMiniLang
makeEffect ''MonadMiniLang ''MonadMiniLangEffect

type MiniLangT m = ExceptT MiniLangError (WriterT String (StateT [MiniLangValue] m))

instance (Monad m) => MonadMiniLang (MiniLangT m) where
  push v = do
    vs <- get
    put (v : vs)
  pop = do
    vs <- get
    case vs of
      [] -> throwError StackUnderflow
      (v : vs') -> do
        put vs'
        return v
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

data Tweak = Tweak
  { onPop :: MiniLangValue -> Maybe MiniLangValue,
    onPush :: MiniLangValue -> Maybe MiniLangValue
  }

instance Semigroup Tweak where
  Tweak fPop fPush <> Tweak gPop gPush =
    Tweak
      (\x -> (fPop <=< gPop) x <|> fPop x <|> gPop x)
      (\x -> (fPush <=< gPush) x <|> fPush x <|> gPush x)

instance (MonadPlus m, MonadError MiniLangError m, MonadMiniLang m) => InterpretLtlHigherOrder Tweak m MonadMiniLangEffect where
  interpretLtlHigherOrder (Push v) = Direct . Apply $ \x ->
    case onPush x v of
      Just v' -> Just <$> push v'
      Nothing -> return Nothing
  interpretLtlHigherOrder Pop = Direct . Apply $ \x -> do
    v <- pop
    case onPop x v of
      Just v' -> return (Just v')
      Nothing -> return Nothing
  interpretLtlHigherOrder Echo {} = Direct Ignore
  interpretLtlHigherOrder (If_ m1 m2) = Nested $ \evalAST ltls ->
    if_ (Just <$> evalAST ltls m1) (Just <$> evalAST ltls m2)
  interpretLtlHigherOrder (While_ m) = Nested $ \evalAST ltls ->
    whileWithFormulas evalAST ltls m
    where
      whileWithFormulas evalAST ltls acts = do
        v <- pop
        msum $
          map
            ( \(now, later) ->
                case now of
                  Nothing -> case v of
                    (MiniLangInteger _) -> throwError ExpectedBoolean
                    (MiniLangBoolean b) ->
                      if b
                        then do
                          ((), ltls') <- evalAST later acts
                          whileWithFormulas evalAST ltls' acts
                        else return $ Just ((), later)
                  Just x -> case onPop x v of
                    Just (MiniLangInteger _) -> throwError ExpectedBoolean
                    Just (MiniLangBoolean b) ->
                      if b
                        then do
                          ((), ltls') <- evalAST later acts
                          whileWithFormulas evalAST ltls' acts
                        else return $ Just ((), later)
                    Nothing -> return Nothing
            )
            (nowLaterList ltls)

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
    -- echo $ show a' ++ ", " ++ show b' ++ "; "
    pushInteger b'
    pushInteger (a' `mod` b')
    pushBoolean (0 /= a' `mod` b')
  _ <- popInteger
  popInteger

flipBools :: Tweak
flipBools =
  let f = \case
        MiniLangBoolean b -> Just $ MiniLangBoolean (not b)
        _ -> Nothing
   in Tweak {onPop = f, onPush = f}

flipIntegers :: Tweak
flipIntegers =
  let f = \case
        MiniLangInteger n -> Just $ MiniLangInteger (-n)
        _ -> Nothing
   in Tweak {onPop = f, onPush = f}

flipBoth :: Tweak
flipBoth = flipBools <> flipIntegers

instance {-# OVERLAPPING #-} (MonadPlus m) => Alternative (MiniLangT m) where
  empty = lift $ lift mzero
  ExceptT (WriterT (StateT f)) <|> ExceptT (WriterT (StateT g)) =
    ExceptT . WriterT . StateT $ \s -> f s `mplus` g s

instance {-# OVERLAPPING #-} (MonadPlus m) => MonadPlus (MiniLangT m)

interpretAndRunMiniLang :: LtlAST Tweak '[MonadMiniLangEffect, MonadErrorEffect MiniLangError] a -> [((Either MiniLangError a, String), [MiniLangValue])]
interpretAndRunMiniLang = runMiniLangT . interpretLtlAST @'[InterpretLtlHigherOrderTag, InterpretEffectStatefulTag]
