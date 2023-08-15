{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Effect.Error.Passthrough where

import Control.Monad.Except
import Effect
import Effect.Error

-- | A "passthough" instance for 'MonadErrorEffect's: Modifications are applied in
-- all nested positions of 'CatchError', but don't actually change the semantics
-- of any 'MonadErrorEffect'.
instance (MonadError e m) => InterpretEffectStateful x m (MonadErrorEffect e) where
  interpretEffectStateful interpAST x (CatchError acts handler) =
    catchError
      (interpAST x acts)
      (interpAST x . handler)
  interpretEffectStateful interpAST x op = (,x) <$> interpretEffect (fmap fst . interpAST x) op
