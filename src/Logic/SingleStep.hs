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
  -- | The mental model of 'interpretMod' assumes a scenario like in the "Ltl"
  -- setting, where there are a (possibly infinite) number of ways to satisfy a
  -- formula, each given by a sequence of atomic modifications to be applied to
  -- the operations of the 'AST'. If all applications of atomic modifications
  -- succeed, that's a successful application of the composite modification
  -- described by the formula.
  --
  -- This big picture is abstracted away here. Everything 'interpretMod' sees
  -- is the current operation, and 'Maybe' an atomic modification. The 'Maybe'
  -- indicates whether we need to apply a modification.
  --
  -- There are the following possibilities, corresponding to the constructors of
  -- 'LtlInterp':
  --
  -- - If you want to try applying the modification, use 'AttemptModification'.
  --   Depending on the current state reached so far, the application of the
  --   modification can fail. Hence, there are two options:
  --
  --   - If the modification successfully applies, return some computation that
  --     returns 'Just'.
  --
  --   - If the modification fails to apply, return 'Nothing'.
  --
  -- - If you don't want to try applying the modification, return 'SkipModification'.
  --   Use this constructor if you don't want to apply the modification to the
  --   current operation, but you still want to continue interpreting the 'AST'
  --   as if the modification had been applied. That is: the current
  --   modification is consumed, and at the next step, the evaluation
  --   continues with the next modification in the sequence. This is most
  --   useful if the current modification is 'Nothing': in this case, you can
  --   use 'SkipModification' to indicate that want to proceed by
  --   \"successfully applying no modification\".
  --
  -- - Like 'SkipModification', 'PassModification' will interpret the operation
  --   without applying the modification. The difference is that the current
  --   modification is /not/ consumed, and at the next step, the evaluation
  --   will continue with the same modification. Another way to think about
  --   'PassModification' is that it makes an operation invisible to the
  --   evaluation of the sequence of atomic modifications. This is useful if
  --   you want "timesteps" to only happen at some operations, and not at
  --   others. Use 'PassModification' for all the operations that don't count
  --   as timesteps.
  --
  -- The @dummy@ type variable signifies that the "nesting" monad of the effect
  -- type is irrelevant, since we're not dealing with higher-order effects.
  interpretMod :: op (AST dummy) a -> Maybe mod -> ModInterp mod m a

-- | Codomain of 'interpretLtl'. See the explanation there.
data ModInterp mod m a = AttemptModification (m (Maybe a)) | SkipModification | PassModification
