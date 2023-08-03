{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Effect.Error where

import Control.Monad.Except
import Effect.TH

data MonadErrorEffect e m a where
  ThrowError :: e -> MonadErrorEffect e m a
  CatchError :: m a -> (e -> m a) -> MonadErrorEffect e m a

makeEffect ''MonadError ''MonadErrorEffect
