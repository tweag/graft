{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Effect.State where

import Control.Monad.State
import Data.Kind
import Effect.TH

data MonadStateEffect s (m :: Type -> Type) a where
  Put :: s -> MonadStateEffect s m ()
  Get :: MonadStateEffect s m s

makeEffect ''MonadState ''MonadStateEffect
