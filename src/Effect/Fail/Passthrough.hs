{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Effect.Fail.Passthrough where

import Effect
import Effect.Fail

-- | A "passthough" instance for 'WriterEffect's: Modifications are applied
-- in all nested positions of 'Listen' and 'Pass', but don't actually change the
-- semantics of any 'WriterEffect'.
instance (MonadFail m) => InterpretEffectStateful x m MonadFailEffect where
  interpretEffectStateful _ x (Fail msg) = (,x) <$> fail msg
