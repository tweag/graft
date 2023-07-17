{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module Fixpoint.IO where

import Control.Monad.IO.Class
import Data.Kind
import Fixpoint.TH

data IOOperation (m :: Type -> Type) a where
  LiftIO :: IO a -> IOOperation m a

makeOperation [t|MonadIO|] [t|IOOperation|]
