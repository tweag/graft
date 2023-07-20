{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}

module Effect.Internal where

import Control.Monad
import Data.Kind

-- * The freer monad

data Freer f a where
  Pure :: a -> Freer f a
  Impure :: f a -> (a -> Freer f b) -> Freer f b

instance Functor (Freer f) where
  fmap g (Pure x) = Pure $ g x
  fmap g (Impure x cont) = Impure x (fmap g . cont)

instance Applicative (Freer f) where
  pure = Pure
  (<*>) = ap

instance Monad (Freer f) where
  (Pure x) >>= g = g x
  (Impure x cont) >>= g = Impure x (cont >=> g)

-- * Fixpoint functors

newtype Fixpoint (f :: (Type -> Type) -> Type -> Type) (g :: (Type -> Type) -> Type -> Type) :: Type -> Type where
  Fixpoint :: {unFixpoint :: f (Fixpoint g f) a} -> Fixpoint f g a

instance (forall h. Functor (f h)) => Functor (Fixpoint f g) where
  fmap f (Fixpoint x) = Fixpoint $ fmap f x

instance (forall h. Applicative (f h)) => Applicative (Fixpoint f g) where
  pure = Fixpoint . pure
  Fixpoint f <*> Fixpoint x = Fixpoint $ f <*> x

instance (forall h. Monad (f h)) => Monad (Fixpoint f g) where
  Fixpoint a >>= f = Fixpoint $ a >>= unFixpoint . f

-- * Interpreting fixpoint functors

class InterpretOneLayer f g m where
  interpretOneLayer :: (forall b. Fixpoint g f b -> m b) -> f (Fixpoint g f) a -> m a

instance (Monad m) => InterpretOneLayer Freer h m where
  interpretOneLayer _ (Pure a) = return a
  interpretOneLayer interpretNextLayer (Impure op cont) = do
    a <- interpretNextLayer op
    interpretOneLayer interpretNextLayer (cont a)

fromFixpoint ::
  (InterpretOneLayer f g m, InterpretOneLayer g f m) =>
  Fixpoint f g a ->
  m a
fromFixpoint = interpretOneLayer fromFixpoint . unFixpoint

fromFixpoint' ::
  (InterpretOneLayer f g m, InterpretOneLayer g f m) =>
  f (Fixpoint g f) a ->
  m a
fromFixpoint' = fromFixpoint . Fixpoint

-- * Interpreting fixpoint functors, statefully

--
-- We could be even more generic and re-use the machinery from the last section,
-- if we're willing to stack another 'StateT' monad transformer. I chose this
-- presentation because it makes the 'InterpretOneLayerState' instance easier to
-- understand.

class InterpretOneLayerState x f g m where
  interpretOneLayerState ::
    (forall b. x -> Fixpoint g f b -> m (b, x)) ->
    x ->
    f (Fixpoint g f) a ->
    m (a, x)

instance (Monad m) => InterpretOneLayerState x Freer h m where
  interpretOneLayerState _ x (Pure a) = return (a, x)
  interpretOneLayerState interpretNextLayer x (Impure op cont) = do
    (a, x') <- interpretNextLayer x op
    interpretOneLayerState interpretNextLayer x' (cont a)

fromFixpointState ::
  (InterpretOneLayerState x f g m, InterpretOneLayerState x g f m) =>
  x ->
  Fixpoint f g a ->
  m (a, x)
fromFixpointState x = interpretOneLayerState fromFixpointState x . unFixpoint

fromFixpointState' ::
  (InterpretOneLayerState x f g m, InterpretOneLayerState x g f m) =>
  x ->
  g (Fixpoint f g) a ->
  m (a, x)
fromFixpointState' x = fromFixpointState x . Fixpoint
