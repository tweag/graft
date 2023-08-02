{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Types and functions wrapping "Fixpoint.Internal" into an user-facing API
module Effect
  ( Effect,
    EffectInject,
    AST,
    astInject,
    InterpretEffect (..),
    InterpretEffects,
    interpretAST,
    InterpretEffectStateful (..),
    InterpretEffectsStateful (..),
    interpretASTStateful,

    -- * Internal
    JoinedEffects (..),
  )
where

import Data.Kind
import Effect.Internal

-- * Effect types

type Effect = (Type -> Type) -> Type -> Type

data JoinedEffects (ops :: [Effect]) :: Effect where
  JoinedEffectsHere :: op m a -> JoinedEffects (op ': ops) m a
  JoinedEffectsThere :: JoinedEffects ops m a -> JoinedEffects (op ': ops) m a

-- | Is the given type of effects an element of the list of effect types?
-- Users won't write instances of this type, they're generated automatically.
--
-- In writing "reification" instances, a useful idiom is something like
--
-- > instance EffectInject (WriterEffect w) ops => MonadWriter (AST ops) where
-- >   ...
--
-- which will define "writer-like syntax" for all lists of effects that
-- contain 'WriterEffect w'. This idiom is also the reason for the functional
-- dependency in the class: @ops@ must contain enough information to determine
-- @op@.
class EffectInject (op :: Effect) (ops :: [Effect]) | ops -> op where
  effectInject :: op m a -> JoinedEffects ops m a

instance {-# OVERLAPPING #-} EffectInject op (op ': ops) where
  effectInject = JoinedEffectsHere

instance (EffectInject x ops) => EffectInject x (y ': ops) where
  effectInject = JoinedEffectsThere . effectInject

-- * Abstract syntax trees for a list of effect types

-- | An abstract syntax tree with effects of type 'op'
type AST ops = Fixpoint Freer (JoinedEffects ops)

-- | convenience function to build the "singleton" 'AST' corresponding to one
-- effect
astInject :: (EffectInject op ops) => op (AST ops) a -> AST ops a
astInject op = Fixpoint $ Impure (Fixpoint . effectInject $ op) Pure

-- * Interpreting 'AST's

-- | Users will write an instance of this class if they want to define the
-- "standard" interpretation of their effect type.
class InterpretEffect m op where
  -- | Given a function that describes how to interpret 'AST's and an effect
  -- that may contain zero or more 'AST's, return the interpretation od the
  -- effect.
  interpretEffect :: (forall b. AST ops b -> m b) -> op (AST ops) a -> m a

data ConstraintList :: (a -> Constraint) -> [a] -> Type where
  ConstraintNil :: ConstraintList c '[]
  ConstraintCons :: (c ty) => ConstraintList c tys -> ConstraintList c (ty ': tys)

-- | The constraint that all effects @ops@ are interpretable (in the sense of
-- 'InterpretEffect') in @m@
class InterpretEffects m ops where
  interpretEffects :: ConstraintList (InterpretEffect m) ops

instance InterpretEffects m '[] where
  interpretEffects = ConstraintNil

instance (InterpretEffect m op, InterpretEffects m ops) => InterpretEffects m (op ': ops) where
  interpretEffects = ConstraintCons interpretEffects

-- | If all effect types in the 'AST' have an 'InterpretEffect m'
-- instance, this function will interpret the 'AST'.
--
-- note: This function is morally the same as 'fromFixpoint', it's just that the
-- instance resolution machinery (especially around the type-level lists of
-- effect states) obfuscates it.
interpretAST :: (Monad m, InterpretEffects m ops) => AST ops a -> m a
interpretAST = interpAST constraintList
  where
    constraintList = interpretEffects

    interpAST :: (Monad m) => ConstraintList (InterpretEffect m) ops -> AST ops a -> m a
    interpAST cs =
      interpretOneLayer
        (interpJoinedOps cs (interpAST cs) . unFixpoint)
        . unFixpoint

    interpJoinedOps ::
      (Monad m) =>
      ConstraintList (InterpretEffect m) ops ->
      (forall b. AST allOps b -> m b) ->
      JoinedEffects ops (AST allOps) a ->
      m a
    interpJoinedOps ConstraintNil _ op = case op of {}
    interpJoinedOps (ConstraintCons _) iAST (JoinedEffectsHere op) = interpretEffect iAST op
    interpJoinedOps (ConstraintCons cs') iAST (JoinedEffectsThere op) = interpJoinedOps cs' iAST op

-- * Interpreting 'AST's, statefully

-- | Users will write an instance of this class if they want to interpret
-- effects of type 'op' in 'm', while also passing a state of type 'x' form
-- step to step. This state will control how effects are implemented.
--
-- For example in "Fixpoint.Examples", I play around with the type of LTL
-- formulas for 'x'.
class InterpretEffectStateful (t :: Type -> Type) m op where
  -- | Given a function that describes how to interpret 'AST's statefully, a
  -- current "interpretation state", and an effect, return the interpretation
  -- of the effect.
  interpretEffectStateful ::
    (forall b y. t y -> AST ops b -> m (b, t y)) ->
    t x ->
    op (AST ops) a ->
    m (a, t x)

-- | The constraint that all effects @ops@ are statefully interpretable (in
-- the sense of 'InterpretEffectStateful') in @m@.
class InterpretEffectsStateful t m ops where
  interpretEffectsStateful :: ConstraintList (InterpretEffectStateful t m) ops

instance InterpretEffectsStateful t m '[] where
  interpretEffectsStateful = ConstraintNil

instance
  (InterpretEffectStateful t m op, InterpretEffectsStateful t m ops) =>
  InterpretEffectsStateful t m (op ': ops)
  where
  interpretEffectsStateful = ConstraintCons interpretEffectsStateful

-- | If all effect types in the 'AST' have an 'InterpretEffectStateful'
-- instance, this function will interpret the 'AST', starting at a given initial
-- "interpretation state"
--
-- note: This function is morally the same as 'fromFixpointState', it's just
-- that the instance resolution machinery (especially around the type-level
-- lists of effect states) obfuscates it.
interpretASTStateful :: (Monad m, InterpretEffectsStateful t m ops) => t x -> AST ops a -> m (a, t x)
interpretASTStateful = interpASTState constraintList
  where
    constraintList = interpretEffectsStateful

    interpASTState ::
      (Monad m) =>
      ConstraintList (InterpretEffectStateful t m) ops ->
      t x ->
      AST ops a ->
      m (a, t x)
    interpASTState cs x =
      interpretOneLayerState
        ( \x' acts ->
            interpJoinedOpsState
              cs
              (interpASTState cs)
              x'
              (unFixpoint acts)
        )
        x
        . unFixpoint

    interpJoinedOpsState ::
      (Monad m) =>
      ConstraintList (InterpretEffectStateful t m) ops ->
      (forall b y. t y -> AST allOps b -> m (b, t y)) ->
      t x ->
      JoinedEffects ops (AST allOps) a ->
      m (a, t x)
    interpJoinedOpsState ConstraintNil _ _ op = case op of {}
    interpJoinedOpsState (ConstraintCons _) iAST x (JoinedEffectsHere op) =
      interpretEffectStateful iAST x op
    interpJoinedOpsState (ConstraintCons cs') iAST x (JoinedEffectsThere op) =
      interpJoinedOpsState cs' iAST x op
