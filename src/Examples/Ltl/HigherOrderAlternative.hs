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
            let vTweaked = case now of
                  Just x -> onPop x v
                  Nothing -> Just v
             in case vTweaked of
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
            let vTweaked = case now of
                  Just x -> onPop x v
                  Nothing -> Just v
             in case vTweaked of
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

popBoolTweak :: (Bool -> Maybe Bool) -> Tweak
popBoolTweak f =
  Tweak
    { onPop = \case
        MiniLangBoolean b -> MiniLangBoolean <$> f b
        _ -> Nothing,
      onPush = const Nothing
    }

popIntegerTweak :: (Integer -> Maybe Integer) -> Tweak
popIntegerTweak f =
  Tweak
    { onPop = \case
        MiniLangInteger n -> MiniLangInteger <$> f n
        _ -> Nothing,
      onPush = const Nothing
    }

popTweak :: (Bool -> Maybe Bool) -> (Integer -> Maybe Integer) -> Tweak
popTweak fBool fInteger = popBoolTweak fBool <> popIntegerTweak fInteger

pushBoolTweak :: (Bool -> Maybe Bool) -> Tweak
pushBoolTweak f =
  Tweak
    { onPop = const Nothing,
      onPush = \case
        MiniLangBoolean b -> MiniLangBoolean <$> f b
        _ -> Nothing
    }

pushIntegerTweak :: (Integer -> Maybe Integer) -> Tweak
pushIntegerTweak f =
  Tweak
    { onPop = const Nothing,
      onPush = \case
        MiniLangInteger n -> MiniLangInteger <$> f n
        _ -> Nothing
    }

pushTweak :: (Bool -> Maybe Bool) -> (Integer -> Maybe Integer) -> Tweak
pushTweak fBool fInteger = pushBoolTweak fBool <> pushIntegerTweak fInteger

flipBools :: Tweak
flipBools = popBoolTweak (Just . not) <> pushBoolTweak (Just . not)

flipIntegers :: Tweak
flipIntegers = popIntegerTweak f <> pushIntegerTweak f
  where
    f 0 = Nothing
    f n = Just $ negate n

flipBoth :: Tweak
flipBoth = flipBools <> flipIntegers

moduloTweak :: Integer -> Tweak
moduloTweak n = popIntegerTweak (Just . (`mod` n)) <> pushIntegerTweak (Just . (`mod` n))

instance {-# OVERLAPPING #-} (MonadPlus m) => Alternative (MiniLangT m) where
  empty = lift $ lift mzero
  ExceptT (WriterT (StateT f)) <|> ExceptT (WriterT (StateT g)) =
    ExceptT . WriterT . StateT $ \s -> f s `mplus` g s

instance {-# OVERLAPPING #-} (MonadPlus m) => MonadPlus (MiniLangT m)

interpretAndRunMiniLang :: LtlAST Tweak '[MonadMiniLangEffect, MonadErrorEffect MiniLangError] a -> [((Either MiniLangError a, String), [MiniLangValue])]
interpretAndRunMiniLang = runMiniLangT . interpretLtlAST @'[InterpretLtlHigherOrderTag, InterpretEffectStatefulTag]
