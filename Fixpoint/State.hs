{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Fixpoint.State where

import Control.Monad.State
import Data.Kind
import Fixpoint.TH
import Language.Haskell.TH hiding (Type)

data StateOperation s (m :: Type -> Type) a where
  Put :: s -> StateOperation s m ()
  Get :: StateOperation s m s

makeOperation [t|MonadState $(varT (mkName "s"))|] [t|StateOperation $(varT (mkName "s"))|]
