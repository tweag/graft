{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Logic.SingleStep
  ( -- * Simple effects
    InterpretMod (..),
    ModInterp (..),
  )
where

import Data.Kind (Type)
import Effect (Effect)

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
  -- | Given an operation of type @op a@, and an atomic modification, there are
  -- three possibilities, corresponding to the constructors of
  -- 'LtlInterp':
  --
  -- - If the modification of the operation should be ignored, and the
  --   operation should just be interpreted without modification, return
  --   'Ignore'.
  --
  -- - If you want to try applying the modification, use return 'Apply':
  --
  --   - If the modification applies, return some computation that returns
  --     'Just'.
  --
  --   - If the modification does /not/ apply, return 'Nothing'.
  --
  --
  -- Note that the type @m (Maybe a)@ (and not @Maybe (m a)@!) in the 'Apply'
  -- constructor means that the interpretation and applicability of the
  -- modification can depend on the state in @m@.
  --
  -- The @dummy@ type variable signifies that the "nesting" monad of the effect
  -- type is irrelevant, since we're not dealing with higher-order effects.
  interpretMod :: op dummy a -> ModInterp mod m a

-- | Codomain of 'interpretLtl'. See the explanation there.
data ModInterp mod m a = Ignore | Apply (mod -> m (Maybe a))
