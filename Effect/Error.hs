{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Effect.Error where

import Control.Monad.Except
import Effect.TH
import Language.Haskell.TH

data ErrorEffect e m a where
  ThrowError :: e -> ErrorEffect e m a
  CatchError :: m a -> (e -> m a) -> ErrorEffect e m a

makeEffect [t|MonadError $(varT (mkName "e"))|] [t|ErrorEffect $(varT (mkName "e"))|]
