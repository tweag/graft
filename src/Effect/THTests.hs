{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

-- | This module only exists to test the TemplateHaskell in "Fixpoint.TH"
module Effect.THTests where

import Data.Kind
import Effect
import Effect.TH

data Foo (m :: Type -> Type) a where
  Foo :: ((m a -> b) -> m c) -> Foo m c

class (Monad m) => MonadFoo m where
  foo :: ((m a -> b) -> m c) -> m c

makeEffect ''MonadFoo ''Foo

-- fooReified :: (EffectInject Foo ops) => ((AST ops a -> b) -> AST ops c) -> AST ops c
-- fooReified x = astInject (Foo x)
--
-- inspect $ mkObligation 'foo CoreOf
-- inspect $ mkObligation 'fooReified CoreOf

interpretFoo :: (MonadFoo m) => (forall b. AST ops b -> m b) -> Foo (AST ops) a -> m a
interpretFoo evalAST (Foo x) = foo (evalAST . x . (. evalAST))

data Bar m a where
  Bar :: (((a -> m b) -> c) -> d) -> Bar m c

class (Monad m) => MonadBar m where
  bar :: (((a -> m b) -> c) -> d) -> m c

makeEffect ''MonadBar ''Bar

data Baz m a where
  Baz :: ((m a -> b) -> m c) -> Baz m c

class (Monad m) => MonadBaz m where
  baz :: ((m a -> b) -> m c) -> m c

makeEffect ''MonadBaz ''Baz

-- -- negative position. this will fail.
-- data Quux m a where
--   Quux :: (m a -> b) -> Quux m c
--
-- class (Monad m) => MonadQuux m where
--   quux :: (m a -> b) -> m c
--
-- makeEffect [t|MonadQuux|] [t|Quux|]

data Quux m a where
  Quux :: Either (IO x, (m a, Bool)) [b -> m a] -> Quux m a

class (Monad m) => MonadQuux m where
  quux :: Either (IO x, (m a, Bool)) [b -> m a] -> m a

makeEffect ''MonadQuux ''Quux
