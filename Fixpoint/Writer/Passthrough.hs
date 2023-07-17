{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Fixpoint.Writer.Passthrough where

import Control.Monad.Writer
import Fixpoint.Api
import Fixpoint.Writer

-- | A "passthough" instance for 'WriterOperation's: Modifications are applied
-- in all nested positions of 'Listen' and 'Pass', but don't actually change the
-- semantics of any 'WriterOperation'.
instance MonadWriter e m => InterpretOperationState x m (WriterOperation e) where
  interpretOperationState interpret x (Listen acts) = do
    ((a, x'), w) <- listen . interpret x $ acts
    return ((a, w), x')
  interpretOperationState interpret x (Pass acts) =
    pass $ do
      ((a, f), x') <- interpret x acts
      return ((a, x'), f)
  interpretOperationState _ x (Tell w) = (,x) <$> tell w
