{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Fixpoint.Error.Passthrough where

import Control.Monad.Except
import Fixpoint.Api
import Fixpoint.Error

-- | A "passthough" instance for 'ErrorOperation's: Modifications are applied in
-- all nested positions of 'CatchError', but don't actually change the semantics
-- of any 'ErrorOperation'.
instance MonadError e m => InterpretOperationState x m (ErrorOperation e) where
  interpretOperationState interpAST x (CatchError acts handler) =
    catchError
      (interpAST x acts)
      (interpAST x . handler)
  interpretOperationState interpAST x op = (,x) <$> interpretOperation (fmap fst . interpAST x) op
