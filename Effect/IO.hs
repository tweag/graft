{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module Effect.IO where

import Control.Monad.IO.Class
import Data.Kind
import Effect.TH

data IOOperation (m :: Type -> Type) a where
  LiftIO :: IO a -> IOOperation m a

makeOperation [t|MonadIO|] [t|IOOperation|]
