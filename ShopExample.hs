{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module ShopExample where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Data.Kind
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Effect
import Effect.Error
import Effect.TH
import Language.Haskell.TH hiding (Type)
import Logic.NextBind

newtype Customer = Customer String deriving (Eq, Ord, Show)

newtype Coins = Coins {getCoins :: Int} deriving (Eq, Ord, Num, Show)

newtype Coupons = Coupons {getCoupons :: Int} deriving (Eq, Ord, Num, Show)

newtype Bananas = Bananas {getBananas :: Int} deriving (Eq, Ord, Num, Show)

data ShopError
  = OutOfBananas
  | NotEnoughPaid
  | NotEnoughCoupons
  deriving (Show, Eq)

class (MonadError ShopError m) => MonadShop m where
  -- | buy some bananas
  buy ::
    -- | who is buying
    Customer ->
    -- | how many coupons to use. Negative amounts mean that you want to buy coupons.
    Coupons ->
    -- | how many coins to use. Must be positive.
    Coins ->
    -- | how many bananas to buy. Must be nonnegative.
    Bananas ->
    m ()

data ShopState = ShopState Coins Bananas (Map Customer Coupons) deriving (Show, Eq)

type ShopT m = ExceptT ShopError (StateT ShopState m)

type Shop = ShopT Identity

instance {-# OVERLAPPING #-} (MonadPlus m) => Alternative (ShopT m) where
  empty = lift $ lift mzero
  (ExceptT (StateT a)) <|> (ExceptT (StateT b)) = ExceptT $ StateT $ \s -> a s `mplus` b s

instance {-# OVERLAPPING #-} (MonadPlus m) => MonadPlus (ShopT m)

-- One coin is worth five bananas, that's why the shop hands out coupons worth
-- one banana each.

instance (Monad m) => MonadShop (ShopT m) where
  buy customer coupons coins bananas = do
    shopState@(ShopState shopCoins shopBananas couponMap) <- get
    case check shopState of
      Nothing ->
        put
          ( ShopState
              (shopCoins + coins)
              (shopBananas - bananas)
              ( case Map.lookup customer couponMap of
                  Nothing ->
                    if
                        | coupons < 0 -> Map.insert customer (-coupons) couponMap
                        | coupons == 0 -> couponMap
                        | otherwise -> error "This can't happen: the check for coupons succeeded, but the customer has none"
                  Just n -> Map.insert customer (n - coupons) couponMap
              )
          )
      Just err -> throwError err
    where
      check :: ShopState -> Maybe ShopError
      check (ShopState _ shopBananas couponMap)
        | shopBananas < bananas = Just OutOfBananas
        | coupons < 0 =
            if 5 * getCoins coins < -getCoupons coupons + getBananas bananas
              then Just NotEnoughPaid
              else Nothing
        | coupons > 0 =
            case Map.lookup customer couponMap of
              Nothing -> Just NotEnoughCoupons
              Just n ->
                if n >= coupons
                  then
                    if 5 * getCoins coins + getCoupons coupons < getBananas bananas
                      then Just NotEnoughPaid
                      else Nothing
                  else Just NotEnoughCoupons
        | 5 * getCoins coins < getBananas bananas = Just NotEnoughPaid -- we know that coupons == 0
        | otherwise = Nothing

runShopT :: ShopState -> ShopT m a -> m (Either ShopError a, ShopState)
runShopT start = flip runStateT start . runExceptT

runShop :: ShopState -> Shop a -> (Either ShopError a, ShopState)
runShop start = runIdentity . runShopT start

initialShopState :: ShopState
initialShopState =
  ShopState
    (Coins 0)
    (Bananas 100)
    mempty

-- (Map.fromList [(Customer "Alice", Coupons 0), (Customer "Bob", Coupons 0)])

data ShopEffect (m :: Type -> Type) (a :: Type) where
  Buy :: Customer -> Coupons -> Coins -> Bananas -> ShopEffect m ()

makeInterpretation (\_ _ -> [t|()|]) ''MonadShop ''ShopEffect

makeReification
  (\_ ops -> [t|EffectInject (ErrorEffect ShopError) $(varT ops)|])
  ''MonadShop
  ''ShopEffect

data Tweak a where
  AskForCoupons :: Tweak Coupons
  UseCoupons :: Coupons -> Tweak ()

instance (MonadShop m) => InterpretNextBind Tweak m ShopEffect where
  interpretNextBind (Buy customer coupons coins bananas) = Direct $
    \case
      AskForCoupons ->
        let delta = getCoins coins * 5 - getBananas bananas
         in if delta >= 0
              then do
                buy customer (-Coupons delta) coins bananas
                return (Just ((), Coupons delta))
              else return Nothing
      UseCoupons n -> do
        buy customer (coupons + n) coins bananas
        return (Just ((), ()))

instance (Monad m) => InterpretNextBind Tweak m (ErrorEffect e) where
  interpretNextBind _ = Direct $ const $ return Nothing

interpretAndRun ::
  NextBind Tweak x ->
  ShopState ->
  AST '[ShopEffect, ErrorEffect ShopError] a ->
  [(Either ShopError (a, NextBind Tweak x), ShopState)]
interpretAndRun modification start = runShopT start . interpretASTStateful modification

interpretRunPrune ::
  NextBind Tweak x ->
  ShopState ->
  AST '[ShopEffect, ErrorEffect ShopError] a ->
  [(Either ShopError a, ShopState)]
interpretRunPrune m s =
  mapMaybe
    ( \case
        (Left err, st) -> Just (Left err, st)
        (Right (a, nb), st) ->
          if finished nb
            then Just (Right a, st)
            else Nothing
    )
    . interpretAndRun m s

trace1 :: (MonadShop m) => m ()
trace1 = buy (Customer "Alice") (Coupons 0) (Coins 2) (Bananas 8)

trace2 :: (MonadShop m) => m ()
trace2 =
  buy (Customer "Alice") (Coupons 0) (Coins 2) (Bananas 8)
    >> buy (Customer "Bob") (Coupons 0) (Coins 3) (Bananas 13)
