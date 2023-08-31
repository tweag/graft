{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Logic.SingleStep
  ( -- * Simple effects
    InterpretMod (..),
    ModInterp (..),
  )
where

import Data.Kind (Type)
import Effect (AST, Effect)

-- | Explain how to interpret an atomic modification, applied an operation of a
-- simple effect type (i.e. one that does not have any higher-order effects).
--
-- - @mod@ is the type of atomic modifications
--
-- - @m@ is a domain into which the modified operation will be interpreted (a
--   monad)
--
-- - @op@ is the effect type.
class InterpretMod (mod :: Type) (m :: Type -> Type) (op :: Effect) where
  -- | 'interpretMod' takes the current operation, an atomic
  -- modification and describes how they should interact.
  --
  -- There are the following possibilities, corresponding to the
  -- constructors of 'LtlInterp':
  --
  -- - If you want to ignore the current operation, make it
  --   'Invisible'. Invisible operations will be ignored by the
  --   modification process, but still executed.
  --
  -- - If you want to try applying the modification, use 'Visible'.
  --   Depending on the current state reached so far, the application
  --   of the modification can fail. Hence, there are two options:
  --
  --   - If the modification successfully applies, return some
  --     computation that returns 'Just'.
  --
  --   - If the modification fails to apply, return 'Nothing'.
  --
  -- The @dummy@ type variable signifies that the "nesting" monad of
  -- the effect type is irrelevant, since we're not dealing with
  -- higher-order effects.
  interpretMod :: op (AST dummy) a -> ModInterp mod m a

-- | Codomain of 'interpretLtl'. See the explanation there.
data ModInterp mod m a
  = Invisible
  | Visible (mod -> m (Maybe a))
