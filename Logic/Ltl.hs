{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Generate state-aware modifications of sequences of stateful actions. The
-- approach is to use an LTL-inspired language to build /composite/
-- modifications that apply /atomic/ modifications to specific steps. Each
-- atomic modification's applicability and parameters may depend on the state
-- reached so far, and there will be zero or more possibilities to apply each
-- composite modification.
--
-- The workflow is to
--
-- - write effect types for all actions that you want to apply atomic
--   modifications to,
--
-- - write an abstract type describing your atomic modifications, together with
--   a 'Semigroup' instance that describes how they combine,
--
-- - write instances of 'InterpretLtl' (or 'InterpretLtlHigherOrder' for
--   higher-order effects) that explain how your atomic modifications apply to
--   your effects,
--
-- - use 'modifyLtl' to apply composite modifications to your trace, and
--
-- - use 'interpretLtlAST' to run all modified versions of your trace.
--
-- The module "Examples.Ltl.Simple" contains a tutorial.
--
-- For historic context, this is a re-implementation of the "LTL" module from
-- cooked-validators. The version this is based upon is:
-- https://github.com/tweag/cooked-validators/blob/a460c1718d8d21bada510d83b705b24b0f8d36e0/src/Cooked/Ltl.hs
module Logic.Ltl
  ( -- * 'Ltl' formulas
    Ltl (..),
    somewhere,
    everywhere,

    -- * Deploying 'Ltl' formulas
    LtlAST,
    modifyLtl,

    -- * Simple effects
    InterpretLtl (..),

    -- * Higher-order effects
    InterpretLtlHigherOrder (..),
    LtlInterp (..),

    -- * Interpreting 'Ltl' modifications
    interpretLtlAST,
    interpretLtlASTWithInitialFormulas,
    InterpretEffectsLtl,
  )
where

import Control.Arrow
import Control.Monad
import Data.Functor.Const
import Data.Kind
import Effect

-- | Type of \"LTL\" formulas. Think of @a@ as a type of atomic
-- \"modifications\", then a value of type @Ltl a@ describes a composite
-- modification that describes where to apply these modifications.
--
-- Since it does not make (obvious) sense to talk of a negated modification or
-- of one modification (possibly in the future) to imply another modification,
-- implication and negation are absent.
data Ltl a
  = -- | The "do nothing" modification that is always applicable
    LtlTruth
  | -- | The modification that never applies
    LtlFalsity
  | -- | The modification that applies a given atomic modification at the
    -- current step
    LtlAtom a
  | -- | Branch into the \"timeline\" where the left modification is applied
    -- and the one where the right modification is applied. (In a sense, this
    -- is an exclusive or, as we do not introduce the branch where both
    -- modifications are applied.)
    LtlOr (Ltl a) (Ltl a)
  | -- | Apply both the left and the right modification. Attention: The \"apply
    -- both\" operation for  atomic modifications of type @a@ will be
    -- user-defined through a @'Semigroup'@ instance. If that operation
    -- isn't commutative, this conjunction may also fail to be commutative.
    LtlAnd (Ltl a) (Ltl a)
  | -- | Apply the given modification at the next step.
    LtlNext (Ltl a)
  | -- | Apply the first modification at least until the second one begins to
    -- be applicable (and is applied), which must happen eventually. The
    -- formulas
    --
    -- > a `LtlUntil` b
    --
    -- and
    --
    -- > b `LtlOr` (a `LtlAnd` LtlNext (a `LtlUntil` b))
    --
    -- are equivalent.
    LtlUntil (Ltl a) (Ltl a)
  | -- | Apply the second modification up to and including the step when the
    -- first one becomes applicable (and is applied); if that never happens,
    -- the second formula will be applied forever. View this as a dual to
    -- 'LtlUntil'. The formulas
    --
    -- > a `LtlRelease` b
    --
    -- and
    --
    -- > b `LtlAnd` (a `LtlOr` LtlNext (a `LtlRelease` b))
    --
    -- are equivalent.
    LtlRelease (Ltl a) (Ltl a)
  deriving (Show)

-- | Apply an atomic modification to some action.
somewhere :: a -> Ltl a
somewhere a = LtlTruth `LtlUntil` LtlAtom a

-- | Apply an atomic modification to all actions.
everywhere :: a -> Ltl a
everywhere a = LtlFalsity `LtlRelease` LtlAtom a

-- | Internal: The effect type corresponding to 'modifyLtl'.
data LtlEffect mod (m :: Type -> Type) a where
  ModifyLtl :: Ltl mod -> m a -> LtlEffect mod m a

-- | An 'AST' that allows modifying parts of its contents with 'Ltl'
-- modifications, using 'modifyLtl'.
type LtlAST mod ops = AST (LtlEffect mod ': ops)

-- | Apply an 'Ltl' modification to an 'LtlAST'. Think of @modifyLtl x acts@ as
-- "try all ways to apply @x@ to the actions given in @acts@".
modifyLtl :: Ltl mod -> LtlAST mod ops a -> LtlAST mod ops a
modifyLtl x acts = astInject $ ModifyLtl x acts

-- | Internal: We pass around a list of 'Ltl' modifications, with the intended
-- meaning that the first formula in the one that was added by the "innermost"
-- 'modifyLtl' (See 'nowLaterList' for how the list modification is applied
-- from step to step). Thus, what we have to do is to add the new formula upon
-- entering the block wrapped by 'ModifyLtl', and check that it's 'finished'
-- upon exiting.
instance
  {-# OVERLAPPING #-}
  (MonadPlus m) =>
  InterpretEffectStateful (Const [Ltl mod]) m (LtlEffect mod)
  where
  interpretEffectStateful evalActs ltls (ModifyLtl ltl acts) = do
    (a, Const ltls') <- evalActs (Const $ ltl : getConst ltls) acts
    if finished . head $ ltls'
      then return (a, Const ltls')
      else mzero

-- | Explain how to interpret an atomic modification, applied an operation of a
-- simple effect type (i.e. one that does not have any higher-order effects).
--
-- - @mod@ is the type of atomic modifications
--
-- - @m@ is a domain into which the modified operation will be interpreted (a
--   monad)
--
-- - @op@ is the effect type.
class InterpretLtl (mod :: Type) (m :: Type -> Type) (op :: Effect) where
  -- | Given an operation of type @op a@, and an atomic modification: If the
  -- modification applies, return 'Just'. If the modification does /not/
  -- apply, return 'Nothing'.
  --
  -- Note that the return type @m (Maybe a)@ (and not @Maybe (m a)@!) means
  -- that the interpretation and applicability of the modification can depend
  -- on the state in @m@.
  --
  -- The @dummy@ type variable signifies that the "nesting" monad of the effect
  -- type is irrelevant, since we're not dealing with higher-order effects.
  interpretLtl :: op dummy a -> mod -> m (Maybe a)

-- | Explain how to interpret an 'Ltl' modification, in the presence of
-- higher-order effects. The type parameters have the same meaning as for
-- 'InterpretLtl'.
class InterpretLtlHigherOrder (mod :: Type) (m :: Type -> Type) (op :: Effect) where
  -- | Given an operation of type @op a@, there are two possibilities,
  -- corresponding the two constructors of 'LtlInterp'.
  --
  -- For simple operations that don't \"nest\" other 'AST's, use the
  -- 'Direct' constructor. Its meaning corresponds precisely to the
  -- 'interpretLtl' function.
  --
  -- For operations that /do/ nest, use the 'Nested' constructor. It needs some
  -- explanation: the stepwise approach based on applying atomic modifications
  -- to single operations breaks down for higher-order operations, since a
  -- single higher-order operation may contain 'AST's of operations. We'll
  -- likely want to use a composite modification while evaluating such nested
  -- 'AST's.
  --
  -- Composite modifications in the current setting are list of 'Ltl' formulas.
  -- Each 'modifyLtl' adds another formula to the head of that list, and all
  -- formulas are evaluated in parallel to the intepretation of the 'AST'.
  -- (That is: if you don't nest 'modifyLtl's, the list will only ever contain
  -- one element. If you nest 'modifyLtl's, the head of the list will be the
  -- formula that was introduced by the innermost 'modifyLtl')
  --
  -- The 'Nested' constructor proposes the following approach: It'll just give
  -- you a function
  --
  -- > evalAST :: forall b. [Ltl mod] -> AST ops b -> m (b, [Ltl mod])
  --
  -- which you can call on the nested 'AST's, which it'll evaluate with the
  -- list of 'Ltl' formulas you provide. To explain it by example, let's use
  -- 'ErrorEffect':
  --
  -- > instance (MonadError e m) => InterpretLtlHigherOrder x m (ErrorEffect e) where
  -- >   interpretLtlHigherOrder (CatchError acts handler) =
  -- >     Nested $ \evalAST ltls ->
  -- >       catchError
  -- >         (evalAST ltls acts)
  -- >         ( \err ->
  -- >             do
  -- >               (a, _) <- evalAST [] $ handler err
  -- >               return (a, ltls)
  -- >         )
  -- >   interpretLtlHigherOrder (ThrowError err) = ...
  --
  -- The equation for 'CatchError' means that you'll interpret the body @acts@
  -- with the composite modification currently in place. If any error is
  -- thrown, you'll run the @handler@, without any modifications at all, and
  -- restore the original composite modification. There might be other ways to
  -- implement this nesting behaviour, depending on your use case, and the
  -- 'Nested' constructor should hopefully be general enough to accommodate
  -- most of them.
  interpretLtlHigherOrder :: op (AST ops) a -> LtlInterp mod m ops a

-- | codomain of 'interpretLtlHigherOrder'. See the explanation there.
data LtlInterp (mod :: Type) (m :: Type -> Type) (ops :: [Effect]) (a :: Type) where
  Direct :: (mod -> m (Maybe a)) -> LtlInterp mod m ops a
  Nested ::
    ( (forall b. [Ltl mod] -> AST ops b -> m (b, [Ltl mod])) ->
      [Ltl mod] ->
      m (a, [Ltl mod])
    ) ->
    LtlInterp mod m ops a

instance (InterpretLtl mod m op) => InterpretLtlHigherOrder mod m op where
  interpretLtlHigherOrder = Direct . interpretLtl

-- | Internal:
instance
  ( Semigroup mod,
    MonadPlus m,
    InterpretEffect m op,
    InterpretLtlHigherOrder mod m op
  ) =>
  InterpretEffectStateful (Const [Ltl mod]) m op
  where
  interpretEffectStateful evalActs (Const ltls) op =
    case interpretLtlHigherOrder op of
      Nested nestFun ->
        second Const
          <$> nestFun
            (\x ast -> second getConst <$> evalActs (Const x) ast)
            ltls
      Direct direct ->
        msum $
          map
            ( \(now, later) ->
                case now of
                  Nothing ->
                    (,Const later)
                      <$> interpretEffect
                        (fmap fst . evalActs (Const []))
                        op
                  Just x -> do
                    mA <- direct x
                    case mA of
                      Nothing -> mzero
                      Just a -> return (a, Const later)
            )
            (nowLaterList ltls)

-- | The constraint that all effect types in @ops@ have an @'InterpretLtl' mod m@
-- or an @'InterpretLtlHigherOrder' mod m@ instance
type InterpretEffectsLtl mod m ops = InterpretEffectsStateful (Const [Ltl mod]) m ops

-- | interpret an 'LtlAST' into a suitable domain
interpretLtlAST :: forall mod m ops a. (Semigroup mod, MonadPlus m, InterpretEffectsLtl mod m ops) => LtlAST mod ops a -> m a
interpretLtlAST = interpretLtlASTWithInitialFormulas ([] @(Ltl mod))

-- | Like 'interpretLtlAST', just with an initial list of 'Ltl' formulas that
-- will be evaluated throughtout the interpretation, even when there are no
-- 'modifyLtl's. Prunes all branches that end with incompletely applied 'Ltl'
-- formulas.
interpretLtlASTWithInitialFormulas :: (Semigroup mod, MonadPlus m, InterpretEffectsLtl mod m ops) => [Ltl mod] -> LtlAST mod ops a -> m a
interpretLtlASTWithInitialFormulas ltls acts = do
  (a, finals) <- interpretASTStateful (Const ltls) acts
  if all finished finals
    then return a
    else mzero

-- | Internal: Split an LTL formula that describes a modification of a
-- computation into a list of @(doNow, doLater)@ pairs, where
--
-- * @doNow@ is @Just@ the modification to be applied to the current time step,
--   or @Nothing@, if no modification needs to be applied,
--
-- * @doLater@ is an LTL formula describing the composite modification that
--   should be applied from the next time step onwards, and
--
-- The return value is a list because a formula might be satisfied in different
-- ways. For example, the modification described by @a `LtlUntil` b@ might be
-- accomplished by applying the modification @b@ right now, or by applying @a@
-- right now and @a `LtlUntil` b@ from the next step onwards; the returned list
-- will contain these two options.
--
-- Modifications should form a 'Semigroup', where '<>' is the composition of
-- modifications. We interpret @a <> b@ as the modification that first applies
-- @b@ and then @a@. Attention: Since we use '<>' to define conjunction, if '<>'
-- is not commutative, conjunction will also fail to be commutative!
nowLater :: (Semigroup a) => Ltl a -> [(Maybe a, Ltl a)]
nowLater LtlTruth = [(Nothing, LtlTruth)]
nowLater LtlFalsity = []
nowLater (LtlAtom g) = [(Just g, LtlTruth)]
nowLater (a `LtlOr` b) = nowLater a ++ nowLater b
nowLater (a `LtlAnd` b) =
  [ ( f <> g,
      ltlSimpl $ c `LtlAnd` d
    )
    | (f, c) <- nowLater a,
      (g, d) <- nowLater b
  ]
nowLater (LtlNext a) = [(Nothing, a)]
nowLater (a `LtlUntil` b) =
  nowLater $ b `LtlOr` (a `LtlAnd` LtlNext (a `LtlUntil` b))
nowLater (a `LtlRelease` b) =
  nowLater $ b `LtlAnd` (a `LtlOr` LtlNext (a `LtlRelease` b))

-- } Internal: If there are no more steps and the next step should satisfy the
-- given formula: Are we finished, i.e. was the initial formula satisfied by
-- now?
finished :: Ltl a -> Bool
finished LtlTruth = True
finished LtlFalsity = False
finished (LtlAtom _) = False
finished (a `LtlAnd` b) = finished a && finished b
finished (a `LtlOr` b) = finished a || finished b
finished (LtlNext _) = False
finished (LtlUntil _ _) = False
finished (LtlRelease _ _) = True

-- | Internal: Say we're passing around more than one formula from each time
-- step to the next, where the intended meaning of a list of formulas is the
-- modification that applies the first formula in the list first, then the
-- second formula, then the third and so on. We'd still like to compute a list
-- of @(doNow, doLater)@ pairs as in 'nowLater', only that the @doLater@ should
-- again be a list of formulas.
nowLaterList :: (Semigroup a) => [Ltl a] -> [(Maybe a, [Ltl a])]
nowLaterList = joinNowLaters . map nowLater
  where
    joinNowLaters [] = [(mempty, [])]
    joinNowLaters (l : ls) =
      [ (g <> f, c : cs)
        | (f, c) <- l,
          (g, cs) <- joinNowLaters ls
      ]

-- | Internal: Straightforward simplification procedure for LTL formulas. This
-- function knows how 'LtlTruth' and 'LtlFalsity' play with conjunction and
-- disjunction and recursively applies this knowledge; it does not do anything
-- "fancy" like computing a normal form and is only used to keep the formulas
-- 'nowLater' generates from growing too wildly.
ltlSimpl :: Ltl a -> Ltl a
ltlSimpl expr =
  let (expr', progress) = simpl expr
   in if progress then expr' else expr
  where
    simpl :: Ltl a -> (Ltl a, Bool)
    simpl (LtlAnd a b) = simplAnd a b
    simpl (LtlOr a b) = simplOr a b
    simpl (LtlNext a) =
      let (a', pa) = simpl a
       in if pa
            then (LtlNext a', True)
            else (LtlNext a, False)
    simpl (LtlUntil a b) = recurse2 LtlUntil a b
    simpl (LtlRelease a b) = recurse2 LtlRelease a b
    simpl x = (x, False)

    simplAnd :: Ltl a -> Ltl a -> (Ltl a, Bool)
    simplAnd a b =
      let (a', pa) = simpl a
          (b', pb) = simpl b
       in case (a', b') of
            (LtlTruth, _) -> (b', True)
            (_, LtlTruth) -> (a', True)
            (LtlFalsity, _) -> (LtlFalsity, True)
            (_, LtlFalsity) -> (LtlFalsity, True)
            _ -> if pa || pb then (LtlAnd a' b', True) else (LtlAnd a b, False)

    simplOr :: Ltl a -> Ltl a -> (Ltl a, Bool)
    simplOr a b =
      let (a', pa) = simpl a
          (b', pb) = simpl b
       in case (a', b') of
            (LtlTruth, _) -> (LtlTruth, True)
            (_, LtlTruth) -> (LtlTruth, True)
            (LtlFalsity, _) -> (b', True)
            (_, LtlFalsity) -> (a', True)
            _ -> if pa || pb then (LtlOr a' b', True) else (LtlOr a b, False)

    recurse2 ::
      (Ltl a -> Ltl a -> Ltl a) ->
      Ltl a ->
      Ltl a ->
      (Ltl a, Bool)
    recurse2 f a b =
      let (a', pa) = simpl a
          (b', pb) = simpl b
       in if pa || pb
            then (f a' b', True)
            else (f a b, False)
