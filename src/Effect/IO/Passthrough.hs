{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Effect.IO.Passthrough where

import Control.Monad.IO.Class
import Effect
import Effect.IO

-- | A "passthough" instance for 'MonadIOEffect's: Modifications don't change anything.
instance (MonadIO m) => InterpretEffectStateful x m MonadIOEffect where
  interpretEffectStateful _ x (LiftIO io) = (,x) <$> liftIO io
