{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# HLINT ignore "Eta reduce" #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Logic.Ltl.TH (makeLtl) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except (runExceptT)
import Control.Monad.Identity (Identity (runIdentity), fix)
import Control.Unification
import Control.Unification.IntVar (evalIntBindingT)
import Control.Unification.Ranked (UFailure (MismatchFailure, OccursFailure))
import Control.Unification.Ranked.IntVar
import Data.Bits (Bits (xor))
import Data.IntMap (IntMap)
import Data.List
import Data.Maybe
import qualified Debug.Trace as Debug
import Effect
import GHC.Generics
import GHC.RTS.Flags (MiscFlags (MiscFlags))
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import Logic.Ltl
import Type.Reflection (TypeRep)

-- | There are three type classes that are relevant for the API in "Logic.Ltl":
--
-- 1. @InterpretLtl mod m op@
--
-- 2. @InterpretLtlHigherOrder mod m op@
--
-- 3. @InterpretEffectStateful (Const [Ltl mod]) m op@
--
-- For each of these classes, if you have an instance, there is a standard way
-- to define instance(s) for the class(es) further down on the list. That is,
-- in principle we could define
--
-- > instance InterpretLtl mod m op => InterpretLtlHigherOrder mod m op
--
-- and
--
-- > instance InterpretLtlHigherOrder mod m op => InterpretEffectStateful (Const [Ltl mod]) m op
--
-- However, we chose not do do this, and provide this macro instead, which
-- defines the "missing" instances on a case-by-case basis. This is because
-- sometimes you want to implement one of the classes further down the list,
-- and do so generally, so that GHC won't be able to pick a most specific
-- instance.
--
-- The macro relies on unification of instance heads: It will only generate
-- instances which are strictly more specific than any pre-existing instance in
-- current scope.
makeLtl :: Q [Dec]
makeLtl = do
  ClassI _ firstInstances <- reify ''InterpretLtl
  ClassI _ higherInstances <- reify ''InterpretLtlHigherOrder
  ClassI _ effectInstances <- reify ''InterpretEffectStateful
  newHigherInstances <-
    makeInstances
      firstInstances
      higherInstances
      ( \ctx firstInstanceHead ->
          case dropSigT firstInstanceHead of
            AppT (AppT (AppT _InterpretLtl modType) domainType) effectType ->
              InstanceD
                Nothing
                ctx
                <$> [t|InterpretLtlHigherOrder $(return modType) $(return domainType) $(return effectType)|]
                <*> ((: []) <$> funD 'interpretLtlHigherOrder [clause [] (NormalB <$> [e|Direct . interpretLtl|]) []])
            _ -> error "malformed 'InterpretLtl' instance head"
      )
  newEffectInstances <-
    makeInstances
      (higherInstances ++ newHigherInstances)
      effectInstances
      ( \ctx higherInstanceHead ->
          case dropSigT higherInstanceHead of
            AppT (AppT (AppT _InterpretLtlHigherOrder modType) domainType) effectType ->
              InstanceD
                Nothing
                <$> ( (++ ctx)
                        <$> sequence
                          [ [t|Semigroup $(return modType)|],
                            [t|MonadPlus $(return domainType)|],
                            [t|InterpretEffect $(return domainType) $(return effectType)|]
                          ]
                    )
                <*> [t|InterpretEffectStateful (Const [Ltl $(return modType)]) $(return domainType) $(return effectType)|]
                <*> ( (: [])
                        <$> funD
                          'interpretEffectStateful
                          [clause [] (NormalB <$> [e|interpretEffectStatefulFromLtlHigherOrder|]) []]
                    )
            _ -> error "malformed 'InterpretLtlHigherOrder' instance head"
      )
  return $ newHigherInstances ++ newEffectInstances
  where
    makeInstances ::
      -- instances of the lower class
      [InstanceDec] ->
      -- instances of the higher class
      [InstanceDec] ->
      -- how to transform the constraints and instance head of the lower class
      -- into an instance of the higher class
      (Cxt -> Type -> Q InstanceDec) ->
      Q [InstanceDec]
    makeInstances lowerInstances higherInstances mkHigherInstance =
      mapMaybeM
        ( \case
            InstanceD _ ctx lowerHead _ -> do
              candidateInstance <- mkHigherInstance ctx lowerHead
              case candidateInstance of
                InstanceD _ _ candidateHead _ ->
                  if any
                    ( \case
                        InstanceD _ _ higherHead _ ->
                          dropSigT higherHead `subsumesType` dropSigT candidateHead
                        _ -> error "expected list of instance declarations"
                    )
                    higherInstances
                    then return Nothing
                    else return $ Just candidateInstance
                _ -> error "malformed instance declaration"
            _ -> error "expected a list of instance declarations"
        )
        lowerInstances
      where
        mapMaybeM :: (Monad m) => (a -> m (Maybe b)) -> [a] -> m [b]
        mapMaybeM _ [] = return []
        mapMaybeM f (x : xs) = do
          my <- f x
          case my of
            Nothing -> mapMaybeM f xs
            Just y -> (y :) <$> mapMaybeM f xs

    -- Remove all occurrences of @SigT t ...@ and replace them with just @t@.
    -- For type unification purposes, we're not interested in a kind
    -- signatures' being there or not.
    dropSigT :: Type -> Type
    dropSigT (ForallT bnd ctx t) = ForallT bnd ctx (dropSigT t)
    dropSigT (ForallVisT bnds t) = ForallVisT bnds (dropSigT t)
    dropSigT (AppT l r) = AppT (dropSigT l) (dropSigT r)
    dropSigT (AppKindT t k) = AppKindT (dropSigT t) k
    dropSigT (SigT t _) = dropSigT t
    dropSigT (InfixT l n r) = InfixT (dropSigT l) n (dropSigT r)
    dropSigT (UInfixT l n r) = UInfixT (dropSigT l) n (dropSigT r)
    dropSigT (ParensT t) = ParensT (dropSigT t)
    dropSigT (ImplicitParamT s t) = ImplicitParamT s (dropSigT t)
    dropSigT t = t

-- * internal helpers

-- ** unifying 'Type's

data TypeFunctor t
  = AppTF t t
  | SigTF t Kind
  | VarTF Name
  | ConTF Name
  | PromotedTF Name
  | ParensTF t
  | TupleTF Int
  | ArrowTF
  | ListTF
  | PromotedTupleTF Int
  | PromotedNilTF
  | PromotedConsTF
  | StarTF
  | ConstraintTF
  | LitTF TyLit
  | WildCardTF
  | ImplicitParamTF String t
  deriving (Functor, Foldable, Traversable, Generic1, Unifiable)

-- | Is the second type a substitution instance of the first one?
subsumesType :: Type -> Type -> Bool
subsumesType a b = case runIdentity . evalIntBindingT . runExceptT @(UFailure TypeFunctor IntVar) $ toUTerm a `subsumes` toUTerm b of
  Left (OccursFailure {}) -> False
  Left (MismatchFailure {}) -> False
  Right x -> x
  where
    toUTerm :: Type -> UTerm TypeFunctor IntVar
    toUTerm (AppT l r) = UTerm $ AppTF (toUTerm l) (toUTerm r)
    toUTerm (SigT t k) = UTerm $ SigTF (toUTerm t) k
    toUTerm (VarT n) = UVar . IntVar . hashString . nameBase $ n
      where
        -- See http://www.cse.yorku.ca/~oz/hash.html for an explanation of the magic numbers.
        hashString :: String -> Int
        hashString = foldl' (\h c -> 33 * h + fromEnum c) 5381
    toUTerm (ConT n) = UTerm $ ConTF n
    toUTerm (PromotedT n) = UTerm $ PromotedTF n
    toUTerm (ParensT t) = UTerm $ ParensTF $ toUTerm t
    toUTerm (TupleT n) = UTerm $ TupleTF n
    toUTerm ArrowT = UTerm ArrowTF
    toUTerm ListT = UTerm ListTF
    toUTerm (PromotedTupleT n) = UTerm $ PromotedTupleTF n
    toUTerm PromotedNilT = UTerm PromotedNilTF
    toUTerm PromotedConsT = UTerm PromotedConsTF
    toUTerm StarT = UTerm StarTF
    toUTerm ConstraintT = UTerm ConstraintTF
    toUTerm (LitT l) = UTerm $ LitTF l
    toUTerm WildCardT = UTerm WildCardTF
    toUTerm (ImplicitParamT s t) = UTerm $ ImplicitParamTF s (toUTerm t)
    toUTerm t = error $ "unification for terms of shape " ++ show t ++ " not (yet) implemented"

-- ** finding the names of type variables in 'data' declarations

getDatatypeVars :: Name -> Q [Name]
getDatatypeVars dtName = do
  DatatypeInfo
    { datatypeInstTypes = instTypes
    } <-
    reifyDatatype dtName
  return $
    map
      ( \case
          VarT name -> name
          SigT (VarT name) _ -> name
          _ -> error "datatype declaration must only have type variables"
      )
      instTypes

getEffectTyVars :: Name -> Q (Name, [Name])
getEffectTyVars effectName = do
  tyVarNames <- getDatatypeVars effectName
  case reverse tyVarNames of
    _ : nestTyVarName : extraTyVarNames -> return (nestTyVarName, reverse extraTyVarNames)
    _ -> error "expecting at least two type arguments in effect type"

getConTName :: Type -> Name
getConTName (ConT name) = name
getConTName (AppT x _) = getConTName x
getConTName _ = error "expecting a type constructor applied to some arguments"
