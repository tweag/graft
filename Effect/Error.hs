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

data ErrorEffect e m a where
  ThrowError :: e -> ErrorEffect e m a
  CatchError :: m a -> (e -> m a) -> ErrorEffect e m a

makeEffect ''MonadError ''ErrorEffect
