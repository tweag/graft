{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Effect.State where

import Control.Monad.State
import Data.Kind
import Effect.TH
import Language.Haskell.TH hiding (Type)

data StateEffect s (m :: Type -> Type) a where
  Put :: s -> StateEffect s m ()
  Get :: StateEffect s m s

makeEffect [t|MonadState $(varT (mkName "s"))|] [t|StateEffect $(varT (mkName "s"))|]
