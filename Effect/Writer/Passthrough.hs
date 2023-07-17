{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Effect.Writer.Passthrough where

import Control.Monad.Writer
import Effect
import Effect.Writer

-- | A "passthough" instance for 'WriterEffect's: Modifications are applied
-- in all nested positions of 'Listen' and 'Pass', but don't actually change the
-- semantics of any 'WriterEffect'.
instance (MonadWriter e m) => InterpretEffectStateful x m (WriterEffect e) where
  interpretEffectStateful interpret x (Listen acts) = do
    ((a, x'), w) <- listen . interpret x $ acts
    return ((a, w), x')
  interpretEffectStateful interpret x (Pass acts) =
    pass $ do
      ((a, f), x') <- interpret x acts
      return ((a, x'), f)
  interpretEffectStateful _ x (Tell w) = (,x) <$> tell w
