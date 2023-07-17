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
  ( OperationInject,
    AST,
    astInject,
    InterpretOperation (..),
    InterpretConstraintList,
    interpretAST,
    InterpretOperationState (..),
    InterpretConstraintListState,
    interpretASTState,
  )
where

import Data.Kind
import Effect.Internal

-- * Lists of operation types

data JoinedOperations (ops :: [(Type -> Type) -> Type -> Type]) :: (Type -> Type) -> Type -> Type where
  JoinedOperationsHere :: op m a -> JoinedOperations (op ': ops) m a
  JoinedOperationsThere :: JoinedOperations ops m a -> JoinedOperations (op ': ops) m a

-- | Is the given type of operations an element of the list of operation types?
-- Users won't write instances of this type, they're generated automatically.
--
-- In writing "reification" instances, a useful idiom is something like
--
-- > instance OperationInject (WriterOperation w) ops => MonadWriter (AST ops) where
-- >   ...
--
-- which will define "writer-like syntax" for all lists of operations that
-- contain 'WriterOperation w'. This idiom is also the reason for the functional
-- dependency in the class: @ops@ must contain enough information to determine
-- @op@.
class OperationInject (op :: (Type -> Type) -> Type -> Type) (ops :: [(Type -> Type) -> Type -> Type]) | ops -> op where
  operationInject :: op m a -> JoinedOperations ops m a

instance {-# OVERLAPPING #-} OperationInject op (op ': ops) where
  operationInject = JoinedOperationsHere

instance (OperationInject x ops) => OperationInject x (y ': ops) where
  operationInject = JoinedOperationsThere . operationInject

-- * Abstract syntax trees for a list of operation types

-- | An abstract syntax tree with operations of type 'op'
type AST ops = Fixpoint Freer (JoinedOperations ops)

-- | convenience function to build the "singleton" 'AST' corresponding to one
-- operation
astInject :: (OperationInject op ops) => op (AST ops) a -> AST ops a
astInject op = Fixpoint $ Impure (Fixpoint . operationInject $ op) Pure

-- * Interpreting 'AST's

-- | Users will write an instance of this class if they want to define the
-- "standard" interpretation of their operation type.
class InterpretOperation m op where
  -- | Given a function that describes how to interpret 'AST's and an operation
  -- that may contain zero or more 'AST's, return the interpretation od the
  -- operation.
  interpretOperation :: (forall b. AST ops b -> m b) -> op (AST ops) a -> m a

data ConstraintList :: (a -> Constraint) -> [a] -> Type where
  ConstraintNil :: ConstraintList c '[]
  ConstraintCons :: (c ty) => ConstraintList c tys -> ConstraintList c (ty ': tys)

-- | The constraint that all operations @ops@ are interpretable (in the sense of
-- 'InterpretOperation') in @m@
class InterpretConstraintList m ops where
  interpretConstraintList :: ConstraintList (InterpretOperation m) ops

instance InterpretConstraintList m '[] where
  interpretConstraintList = ConstraintNil

instance (InterpretOperation m op, InterpretConstraintList m ops) => InterpretConstraintList m (op ': ops) where
  interpretConstraintList = ConstraintCons interpretConstraintList

-- | If all operation types in the 'AST' have an 'InterpretOperation m'
-- instance, this function will interpret the 'AST'.
--
-- note: This function is morally the same as 'fromFixpoint', it's just that the
-- instance resolution machinery (especially around the type-level lists of
-- operation states) obfuscates it.
interpretAST :: (Monad m, InterpretConstraintList m ops) => AST ops a -> m a
interpretAST = interpAST constraintList
  where
    constraintList = interpretConstraintList

    interpAST :: (Monad m) => ConstraintList (InterpretOperation m) ops -> AST ops a -> m a
    interpAST cs =
      interpretOneLayer
        (interpJoinedOps cs (interpAST cs) . unFixpoint)
        . unFixpoint

    interpJoinedOps ::
      (Monad m) =>
      ConstraintList (InterpretOperation m) ops ->
      (forall b. AST allOps b -> m b) ->
      JoinedOperations ops (AST allOps) a ->
      m a
    interpJoinedOps ConstraintNil _ op = case op of {}
    interpJoinedOps (ConstraintCons _) iAST (JoinedOperationsHere op) = interpretOperation iAST op
    interpJoinedOps (ConstraintCons cs') iAST (JoinedOperationsThere op) = interpJoinedOps cs' iAST op

-- * Interpreting 'AST's, statefully

-- | Users will write an instance of this class if they want to interpret
-- operations of type 'op' in 'm', while also passing a state of type 'x' form
-- step to step. This state will control how operations are implemented.
--
-- For example in "Fixpoint.Examples", I play around with the type of LTL
-- formulas for 'x'.
class InterpretOperationState t m op where
  -- | Given a function that describes how to interpret 'AST's statefully, a
  -- current "interpretation state", and an operation, return the interpretation
  -- of the operation.
  interpretOperationState ::
    (forall b y. t y -> AST ops b -> m (b, t y)) ->
    t x ->
    op (AST ops) a ->
    m (a, t x)

-- | The constraint that all operations @ops@ are statefully interpretable (in
-- the sense of 'InterpretOperationState') in @m@.
class InterpretConstraintListState t m ops where
  interpretConstraintListState :: ConstraintList (InterpretOperationState t m) ops

instance InterpretConstraintListState t m '[] where
  interpretConstraintListState = ConstraintNil

instance
  (InterpretOperationState t m op, InterpretConstraintListState t m ops) =>
  InterpretConstraintListState t m (op ': ops)
  where
  interpretConstraintListState = ConstraintCons interpretConstraintListState

-- | If all operation types in the 'AST' have an 'InterpretOperationState'
-- instance, this function will interpret the 'AST', starting at a given initial
-- "interpretation state"
--
-- note: This function is morally the same as 'fromFixpointState', it's just
-- that the instance resolution machinery (especially around the type-level
-- lists of operation states) obfuscates it.
interpretASTState :: (Monad m, InterpretConstraintListState t m ops) => t x -> AST ops a -> m (a, t x)
interpretASTState = interpASTState constraintList
  where
    constraintList = interpretConstraintListState

    interpASTState ::
      (Monad m) =>
      ConstraintList (InterpretOperationState t m) ops ->
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
      ConstraintList (InterpretOperationState t m) ops ->
      (forall b y. t y -> AST allOps b -> m (b, t y)) ->
      t x ->
      JoinedOperations ops (AST allOps) a ->
      m (a, t x)
    interpJoinedOpsState ConstraintNil _ _ op = case op of {}
    interpJoinedOpsState (ConstraintCons _) iAST x (JoinedOperationsHere op) =
      interpretOperationState iAST x op
    interpJoinedOpsState (ConstraintCons cs') iAST x (JoinedOperationsThere op) =
      interpJoinedOpsState cs' iAST x op
