{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Effect.Internal where

import Control.Monad
import Data.Kind

-- * The freer monad

data Freer f a where
  Pure :: a -> Freer f a
  Impure :: f a -> (a -> Freer f b) -> Freer f b

instance Functor (Freer f) where
  fmap g (Pure x) = Pure $ g x
  fmap g (Impure x cont) = Impure x (fmap g . cont)

instance Applicative (Freer f) where
  pure = Pure
  (<*>) = ap

instance Monad (Freer f) where
  (Pure x) >>= g = g x
  (Impure x cont) >>= g = Impure x (cont >=> g)

-- * Fixpoint functors

-- $doc
-- This is a generalisation/analogy with constructions like
--
-- > data Fix = f (Fix f)
--
-- Here, @f@ is of kind @Type -> Type@. The first insight is that this works
-- for arbitrary kinds @k@, i.e. for any @f :: k -> k@. The second step is
-- noting that for @k = Type -> Type@, we can also build something that
-- alternates between to @f@s. This is that type:

newtype Fixpoint (f :: (Type -> Type) -> Type -> Type) (g :: (Type -> Type) -> Type -> Type) :: Type -> Type where
  Fixpoint :: {unFixpoint :: f (Fixpoint g f) a} -> Fixpoint f g a

instance (forall h. Functor (f h)) => Functor (Fixpoint f g) where
  fmap f (Fixpoint x) = Fixpoint $ fmap f x

instance (forall h. Applicative (f h)) => Applicative (Fixpoint f g) where
  pure = Fixpoint . pure
  Fixpoint f <*> Fixpoint x = Fixpoint $ f <*> x

instance (forall h. Monad (f h)) => Monad (Fixpoint f g) where
  Fixpoint a >>= f = Fixpoint $ a >>= unFixpoint . f

-- * Interpreting fixpoint functors layer by layer

-- | The idea of this class: If you have @InterpretOneLayer f g m@ and
-- @InterpretOneLayer g f m@, it's pretty easy to obtain a function
--
-- >  interpretFixpoint ::
-- >    (InterpretOneLayer f g m, InterpretOneLayer g f m) =>
-- >    Fixpoint f g a ->
-- >    m a
-- >  fromFixpoint = interpretOneLayer fromFixpoint . unFixpoint
--
-- which calls the two 'interpretOneLayer' functions mutually recursively.
class InterpretOneLayer f g m where
  interpretOneLayer :: (forall b. Fixpoint g f b -> m b) -> f (Fixpoint g f) a -> m a

instance (Monad m) => InterpretOneLayer Freer h m where
  interpretOneLayer _ (Pure a) = return a
  interpretOneLayer interpretNextLayer (Impure op cont) = do
    a <- interpretNextLayer op
    interpretOneLayer interpretNextLayer (cont a)

-- * Interpreting fixpoint functors layer by layer, statefully

-- $doc
-- We could be even more generic and re-use the machinery from the last
-- section, if we're willing to stack another 'StateT' monad transformer. I
-- chose this presentation because it makes 'interpretOneLayerState' easier to
-- understand and use later on.

class InterpretOneLayerState x f g m where
  interpretOneLayerState ::
    (forall b. x -> Fixpoint g f b -> m (b, x)) ->
    x ->
    f (Fixpoint g f) a ->
    m (a, x)

instance (Monad m) => InterpretOneLayerState x Freer h m where
  interpretOneLayerState _ x (Pure a) = return (a, x)
  interpretOneLayerState interpretNextLayer x (Impure op cont) = do
    (a, x') <- interpretNextLayer x op
    interpretOneLayerState interpretNextLayer x' (cont a)

-- * Effect types

-- | The kind of effects.
type Effect = (Type -> Type) -> Type -> Type

-- | A list of 'Effect's, treated as a single 'Effect'.
data JoinedEffects (ops :: [Effect]) :: Effect where
  JoinedEffectsHere :: op m a -> JoinedEffects (op ': ops) m a
  JoinedEffectsThere :: JoinedEffects ops m a -> JoinedEffects (op ': ops) m a

-- | Is a given type of effects an element of a list of effect types?
--
-- In writing "reification" instances, a useful idiom is something like
--
-- > instance EffectInject (MonadWriterEffect w) ops => MonadWriter (AST ops)
--
-- which will define "writer-like syntax" for all lists of effects that
-- contain 'WriterEffect w'. This idiom is also the reason for the functional
-- dependency in the class: @ops@ must contain enough information to determine
-- @op@.
--
-- Users of the library should't write instances of this type, as they're
-- generated automatically. Also, "reification" instances like the one above
-- aren't written by hand, usually. Macros like 'makeEffect' do this.
class EffectInject (op :: Effect) (ops :: [Effect]) | ops -> op where
  effectInject :: op m a -> JoinedEffects ops m a

instance {-# OVERLAPPING #-} EffectInject op (op ': ops) where
  effectInject = JoinedEffectsHere

instance (EffectInject x ops) => EffectInject x (y ': ops) where
  effectInject = JoinedEffectsThere . effectInject

-- * Abstract syntax trees for a list of effect types

-- | An abstract syntax tree which may use 'Effect's of types 'ops'
type AST ops = Fixpoint Freer (JoinedEffects ops)

-- | Low-level convenience function to build the "singleton" 'AST'
-- corresponding to one effect.
astInject :: (EffectInject op ops) => op (AST ops) a -> AST ops a
astInject op = Fixpoint $ Impure (Fixpoint . effectInject $ op) Pure

-- * Interpreting 'AST's

-- | Write an instance of this class to define the "standard" interpretation of
-- an effect type into a suitable domain.
--
-- If you want to use the function 'interpretAST', this class has to be
-- implemented for all effect types you're using in your 'AST'. In the normal
-- case, you won't do this by hand, but generate the instance (and others)
-- using a macro like 'makeEffect'.
--
-- Compared to logics like "Logic.Ltl", this is a low-level class; in the
-- standard applications of these logics, you'll never have to directly
-- interact with this class.
class InterpretEffect m op where
  -- | Given a function that describes how to interpret 'AST's and an effect,
  -- return the interpretation of the effect.
  interpretEffect :: (forall b. AST ops b -> m b) -> op (AST ops) a -> m a

-- | A list of constraints, reified as a datatype. Matching on the constructors
-- will bring the constraints in scope.
--
-- This trick is used in the functions 'interpretAST' and
-- 'interpretASTStateful': while deconstructing the 'JoinedEffects' to obtain
-- the individual effects to be interpreted through their 'InterpretEffect' (or
-- 'InterpretEffectStateful') instances, the instances are brought into scope
-- by deconstructing a matching 'ConstraintList'.
data ConstraintList :: (a -> Constraint) -> [a] -> Type where
  ConstraintNil :: ConstraintList c '[]
  ConstraintCons :: (c ty) => ConstraintList c tys -> ConstraintList c (ty ': tys)

-- | The constraint that all effects @ops@ are interpretable (in the sense of
-- 'InterpretEffect') into @m@.
--
-- You should never have to manually write an instance of this class, it should
-- always be inferred.
class InterpretEffects m ops where
  interpretEffects :: ConstraintList (InterpretEffect m) ops

instance InterpretEffects m '[] where
  interpretEffects = ConstraintNil

instance (InterpretEffect m op, InterpretEffects m ops) => InterpretEffects m (op ': ops) where
  interpretEffects = ConstraintCons interpretEffects

-- | If all effect types in @ops@ have an @InterpretEffect m@ instance, this
-- function will interpret the 'AST' into 'm'.
interpretAST :: (Monad m, InterpretEffects m ops) => AST ops a -> m a
interpretAST = interpAST constraintList
  where
    constraintList = interpretEffects

    interpAST :: (Monad m) => ConstraintList (InterpretEffect m) ops -> AST ops a -> m a
    interpAST cs =
      interpretOneLayer
        (interpJoinedEffs cs (interpAST cs) . unFixpoint)
        . unFixpoint

    interpJoinedEffs ::
      (Monad m) =>
      ConstraintList (InterpretEffect m) ops ->
      (forall b. AST allOps b -> m b) ->
      JoinedEffects ops (AST allOps) a ->
      m a
    interpJoinedEffs ConstraintNil _ op = case op of {}
    interpJoinedEffs (ConstraintCons _) iAST (JoinedEffectsHere op) =
      interpretEffect iAST op
    interpJoinedEffs (ConstraintCons cs') iAST (JoinedEffectsThere op) =
      interpJoinedEffs cs' iAST op

-- * Interpreting 'AST's, statefully

-- | Write an instance of this class to define the "statefully modified"
-- interpretation of an effect type into a suitable domain. The intuition is
-- that you interpret effects of type @ops@ into the domain @m@, while also
-- passing a state of type @t x@ from step to step. This state will control how
-- effects are actually implemented in @m@.
--
-- If you want to use the function 'interpretASTStateful', this class has to be
-- implemented for all effect types in the 'AST' you're using.
--
-- Compared to logics like "Logic.Ltl", this is a low-level class; in the
-- standard applications of these logics, you'll never have to directly
-- interact with this class.
class InterpretEffectStateful (t :: Type -> Type) m op where
  -- | Given a function that describes how to interpret 'AST's statefully, a
  -- current "interpretation state", and an effect, return the stateful
  -- interpretation of the effect.
  interpretEffectStateful ::
    (forall b y. t y -> AST ops b -> m (b, t y)) ->
    t x ->
    op (AST ops) a ->
    m (a, t x)

-- | The constraint that all effects @ops@ are statefully interpretable with a
-- state of type @t@  into @m@ (in the sense of 'InterpretEffectStateful').
--
-- You should never have to manually write an instance of this class, it should
-- always be inferred.
class InterpretEffectsStateful t m ops where
  interpretEffectsStateful :: ConstraintList (InterpretEffectStateful t m) ops

instance InterpretEffectsStateful t m '[] where
  interpretEffectsStateful = ConstraintNil

instance
  (InterpretEffectStateful t m op, InterpretEffectsStateful t m ops) =>
  InterpretEffectsStateful t m (op ': ops)
  where
  interpretEffectsStateful = ConstraintCons interpretEffectsStateful

-- | If all effect types in @ops@ have an @InterpretEffectStateful t m@
-- instance, this function will interpret the 'AST', starting at a given
-- initial "interpretation state" of type @t x@ for some @x@.
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
            interpJoinedEffsState
              cs
              (interpASTState cs)
              x'
              (unFixpoint acts)
        )
        x
        . unFixpoint

    interpJoinedEffsState ::
      (Monad m) =>
      ConstraintList (InterpretEffectStateful t m) ops ->
      (forall b y. t y -> AST allOps b -> m (b, t y)) ->
      t x ->
      JoinedEffects ops (AST allOps) a ->
      m (a, t x)
    interpJoinedEffsState ConstraintNil _ _ op = case op of {}
    interpJoinedEffsState (ConstraintCons _) iAST x (JoinedEffectsHere op) =
      interpretEffectStateful iAST x op
    interpJoinedEffsState (ConstraintCons cs') iAST x (JoinedEffectsThere op) =
      interpJoinedEffsState cs' iAST x op
