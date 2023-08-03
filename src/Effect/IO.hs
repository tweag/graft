{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Effect.IO where

import Control.Monad.IO.Class
import Data.Kind
import Effect.TH

data MonadIOEffect (m :: Type -> Type) a where
  LiftIO :: IO a -> MonadIOEffect m a

makeEffect ''MonadIO ''MonadIOEffect
