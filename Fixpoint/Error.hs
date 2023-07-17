{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Fixpoint.Error where

import Control.Monad.Except
import Fixpoint.TH
import Language.Haskell.TH

data ErrorOperation e m a where
  ThrowError :: e -> ErrorOperation e m a
  CatchError :: m a -> (e -> m a) -> ErrorOperation e m a

makeOperation [t|MonadError $(varT (mkName "e"))|] [t|ErrorOperation $(varT (mkName "e"))|]
