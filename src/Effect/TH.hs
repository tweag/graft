{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Effect.TH
  ( makeEffect,
    makeReification,
    makeInterpretation,
  )
where

import Control.Monad
import Data.Bifunctor
import Data.Char (toLower)
import qualified Data.Map as Map
import Effect
import Language.Haskell.TH
import Language.Haskell.TH.Datatype

-- | Automatically write "reification" and "interpretation" instances for an
-- effect type and its associated class of monads.
--
-- Assume a class definition like
--
-- > class (SomeConstraint a, MonadBar b m) => MonadFoo a b m
--
-- and an effect type defined like
--
-- > data MonadFooEffect a b :: Effect
--
-- Then the macro
--
-- > makeEffect ''MonadFoo ''MonadFooEffect
--
-- will expand into two instance definitions:
--
-- 1. The "reification" instance
--
-- > instance (SomeConstraint a,
-- >           EffectInject (MonadBarEffect b) ops,
-- >           EffectInject (MonadFooEffect a b) ops)
-- >   => MonadFoo a b (AST ops)
--
-- says that an 'AST' whose list @ops@ of effect types contains
-- @MonadFooEffect@ is a @MonadFoo@. In order for this instance to make sense,
-- though, we'll have to add at least satisfy the constraints that were already
-- there on the class definition of @MonadFoo@. Therefore, we have to add
--
-- - @SomeConstraint a@,
--
-- - a constraint that implies @MonadBar b (AST ops)@: That is the reason for
--   the constraint @EffectInject (MonadBarEffect b) ops@. This macro assumes
--   that the only way for an 'AST' to become a @MonadX@ for some @X@ is to
--   contain the correct effect type @MonadXEffect@. That is we employ a
--
-- __naming convention__: The effect type corresponding to the class @X@ is
-- called @XEffect@. For example, 'MonadError' corresponds to
-- 'MonadErrorEffect'.
--
-- while we're at it, there's another
--
-- __naming convention__: The names of the constructors of @XEffect@ must be
-- exactly the names of the methods of the class @X@, just starting with an
-- upper-case letter.
--
-- 2.  the "interpretation" instance
--
-- > instance (MonadFoo a b m) => InterpretEffect m (MonadFooEffect a b)
--
-- says that for any @MonadFoo a b m@, we can interpret the effects described
-- by @MonadFooEffect a b@ into @m@.
--
--
-- /remark for the general case/: This macro works by using the "additional
-- constraints" arguments to 'makeReification' and 'makeInterpretation'. If you
-- want to generate the instances with other constraints, you'll have to use
-- these two macros directly.
makeEffect :: Name -> Name -> Q [Dec]
makeEffect className effectName = do
  ClassI (ClassD ctx _ vars _ _) _ <- reify className
  let names =
        map
          ( \case
              PlainTV x _ -> x
              KindedTV x _ _ -> x
          )
          vars
      -- The context of the class definition (i.e. its constraints, as a
      -- function of the type variables used. The list of 'Name's containss all
      -- of the "extra" type variables, and the singular 'Name' is the name of
      -- the monad @m@.
      ctxAsFunction :: [Name] -> Name -> [Type]
      ctxAsFunction extraNames mName =
        applySubstitution
          (Map.fromList $ zip names (VarT <$> extraNames ++ [mName]))
          ctx
  d1 <- makeReification (reificationExtraConstraints ctxAsFunction) className effectName
  d2 <- makeInterpretation (interpretationExtraConstraints ctxAsFunction) className effectName
  return $ d1 ++ d2
  where
    reificationExtraConstraints,
      interpretationExtraConstraints ::
        ([Name] -> Name -> [Type]) -> [Name] -> Name -> Q Type

    reificationExtraConstraints ctx extraNames opsName = do
      dummyName <- newName "dummy"
      bigTuple
        <$> mapMaybeM
          ( \constraint ->
              if dummyName `elem` freeVariables constraint
                then case constraint of
                  AppT c x
                    | x == VarT dummyName ->
                        if c /= ConT ''Monad
                          then Just <$> [t|EffectInject $(return (onFirst mkEffectName c)) $(varT opsName)|]
                          else return Nothing
                  _ -> error $ "The class '" ++ nameBase className ++ "' has a constraint where the \"monad\" argument isn't the last. The TH can't (yet) handle this. Try using 'makeInterpretation' and 'makeReification' directly"
                else return $ Just constraint
          )
          (ctx extraNames dummyName)

    interpretationExtraConstraints _ _ _ = [t|()|]

    -- on a type constructor applied to some arguments apply some
    -- transformation to the name of the constructor
    onFirst :: (Name -> Name) -> Type -> Type
    onFirst f (ConT n) = ConT $ f n
    onFirst f (AppT a b) = AppT (onFirst f a) b
    onFirst _ _ = error "expected a type constructor applied to some arguments"

    -- make a big tuple of the form (...((((), a), b), c) ...) out of a list like [a, b, c]
    bigTuple :: [Type] -> Type
    bigTuple = foldl (\a b -> AppT (AppT (TupleT 2) a) b) (TupleT 0)

-- | Write a "reification" instance for an effect type. Such an instance
-- allows writing 'AST's containing effects of that type using the syntax of
-- a class like 'MonadError', 'MonadState'...
--
-- For example, given the effect type
--
-- > data ErrorEffect e m a where
-- >   ThrowError :: e -> ErrorEffect e m a
-- >   CatchError :: m a -> (e -> m a) -> ErrorEffect e m a
--
-- the TH splice
--
-- > makeReification
-- >   (\[e] ops -> [t|SomeConstraint $(varT e) $(varT ops)|])
-- >   ''MonadError
-- >   ''ErrorEffect
--
-- will expand into an instance like
--
-- > instance (SomeConstraint e ops, EffectInject (ErrorEffect e) ops) => MonadError e (AST ops) where
-- >   throwError err = astInject (ThrowError err)
-- >   catchError acts handler = astInject (CatchError acts handler)
--
-- For this to work, it is expected that:
--
-- - The first quoted type passed to the splice is the class that you want to
--   use for your syntax. Its kind should be @(* -> *) -> Constraint@
--
-- - The second quoted type is the effect type.
--   Its kind should be @(* -> *) -> * -> *@.
--
-- - The constructor names of the effect type are exactly the method names
--   of the class, just beginning with an upper case letter.
makeReification ::
  -- | additional constraints for the instance head, depending on the names of
  -- extra type variables belonging to the effect type, and of @ops@
  ([Name] -> Name -> Q Type) ->
  -- | class name
  Name ->
  -- | the effect type
  Name ->
  Q [Dec]
makeReification qExtraConstraints className effectName = do
  opsName <- newName "ops"
  let ops = VarT opsName
  DatatypeInfo
    { datatypeInstTypes = instTypes, -- we expect at least two types here, namely the "nesting" monad, and the return value
      datatypeCons = constructors
    } <-
    reifyDatatype effectName
  let tyVarNames =
        -- all type variables that the type constructor is applied to
        map
          ( \case
              VarT name -> name
              SigT (VarT name) _ -> name
              _ -> error "effect datatype declaration must only have type variables"
          )
          instTypes
  let extraTyVarNames = case reverse tyVarNames of
        _ : _ : l -> reverse l
        _ -> error "expecting at least two type arguments in effect type"
  extraConstraints <- qExtraConstraints extraTyVarNames opsName
  methodImplementations <- mapM (matchAndHandleConstructor opsName extraTyVarNames) constructors
  return
    [ InstanceD
        Nothing
        [ extraConstraints,
          AppT
            ( AppT
                (ConT ''EffectInject)
                ( foldl
                    (\t n -> AppT t (VarT n))
                    (ConT effectName)
                    extraTyVarNames
                )
            )
            ops
        ]
        ( AppT
            ( foldl
                (\t n -> AppT t (VarT n))
                (ConT className)
                extraTyVarNames
            )
            (AppT (ConT ''AST) ops)
        )
        methodImplementations
    ]
  where
    matchAndHandleConstructor :: Name -> [Name] -> ConstructorInfo -> Q Dec
    matchAndHandleConstructor _ _ ConstructorInfo {constructorVariant = InfixConstructor} =
      error "infix constructors for effects not (yet) supported"
    matchAndHandleConstructor
      opsName
      extraTyVarNames
      ConstructorInfo {constructorName = name, constructorFields = argTypes} =
        handleConstructor opsName extraTyVarNames name (length argTypes)

    handleConstructor :: Name -> [Name] -> Name -> Int -> Q Dec
    handleConstructor opsName extraTyVarNames cName argc = do
      varNames <- replicateM argc (newName "x")
      return $
        FunD
          (lowerFirst cName)
          [ Clause
              (map VarP varNames)
              ( NormalB
                  $ AppE
                    ( AppTypeE
                        ( AppTypeE
                            (VarE 'astInject)
                            ( foldl
                                (\t n -> AppT t (VarT n))
                                (ConT effectName)
                                extraTyVarNames
                            )
                        )
                        (VarT opsName)
                    )
                  $ foldl
                    (\expr argName -> AppE expr (VarE argName))
                    (ConE cName)
                    varNames
              )
              []
          ]

-- | Write an "interpretation" instance for an effect type. Such an instance
-- allows one to evaluate 'AST's using the effect type. (For example, using 'interpretAST')
--
-- For example, given the effect type
--
-- > data ErrorEffect e m a where
-- >   ThrowError :: e -> ErrorEffect e m a
-- >   CatchError :: m a -> (e -> m a) -> ErrorEffect e m a
--
-- the TH splice
--
-- > makeInterpretation (\[e] m -> [t|SomeConstraint $(varT e) $(varT m)|]) [t|ErrorEffect $(varT (mkName "e"))|]
--
-- will expand into an instance like
--
-- > instance (SomeConstraint e m, MonadError e m) => InterpretEffect m (ErrorEffect e) where
-- >   interpretEffect _ (ThrowError err) = throwError @e err
-- >   interpretEffect evalAST (CatchError acts handler) = catchError @e (evalAST acts) (evalAST . handler)
--
-- For this to work, it is expected that:
--
-- - The first quoted type passed to the splice is the class of monads that yow
--   want to interpret the effect into. Its kind should be @(* -> *) ->
--   Constraint@
--
-- - The second quoted type is the effect type.
--   Its kind should be @(* -> *) -> * -> *@.
--
-- - The constructor names of the effect type are exactly the method names
--   of the class, just beginning with an upper case letter.
--
-- - The arguments of constructors of the effect type only use @m@ in
--   positive positions. This is not a restriction of the TemplateHaskell, but a
--   restriction of the library. You can only "nest" 'AST's in positive position.
--
-- - For now, the TemplateHaskell works only if the arguments of constructors
--   of the effect type only use the following type constructors:
--     - The name of the "nesting" monad (here, that's @m@) applied to some type
--     - Function Types (i.e. @->@, or 'ArrowT' in TH)
--     - List Types (i.e. 'ListT' in TH)
--     - @Maybe@, @Either@, or @(,)@ applied to some type(s)
--     - @IO@ applied to some type
--     - Parenheses (i.e. 'ParensT' in TH)
--     - Type Variables (i.e. 'VarT' in TH)
--     - Type Constructors of types of kind @*@
makeInterpretation ::
  -- | additional constraints for the instance head, depending on the names of
  -- extra type variables belonging to the effect type, and of @m@
  ([Name] -> Name -> Q Type) ->
  -- | class name
  Name ->
  -- | effect type name
  Name ->
  Q [Dec]
makeInterpretation qExtraConstraints className effectName = do
  mName <- newName "m"
  let m = VarT mName
  DatatypeInfo
    { datatypeInstTypes = instTypes, -- we expect at least two types here, namely the "nesting" monad, and the return value
      datatypeCons = constructors
    } <-
    reifyDatatype effectName
  let tyVarNames =
        -- all type variables that the type constructor is applied to
        map
          ( \case
              VarT name -> name
              SigT (VarT name) _ -> name
              _ -> error "effect datatype declaration must only have type variables"
          )
          instTypes
  let (nestVarName, extraTyVarNames) = case reverse tyVarNames of
        _ : x : l -> (x, reverse l)
        _ -> error "expecting at least two type arguments in effect type"
  extraConstraints <- qExtraConstraints extraTyVarNames mName
  implementation <- FunD 'interpretEffect <$> mapM (matchAndHandleConstructor extraTyVarNames nestVarName) constructors
  return
    [ InstanceD
        Nothing
        [ extraConstraints,
          foldl
            (\t n -> AppT t (VarT n))
            (ConT className)
            (extraTyVarNames ++ [mName])
        ]
        ( AppT
            (AppT (ConT ''InterpretEffect) m)
            (foldl (\t n -> AppT t (VarT n)) (ConT effectName) extraTyVarNames)
        )
        [implementation]
    ]
  where
    matchAndHandleConstructor :: [Name] -> Name -> ConstructorInfo -> Q Clause
    matchAndHandleConstructor _ _ ConstructorInfo {constructorVariant = InfixConstructor} =
      error "infix constructors for effects not (yet) supported"
    matchAndHandleConstructor
      extraTyVarNames
      nestVarName
      ConstructorInfo {constructorName = name, constructorFields = argTypes} =
        handleConstructor extraTyVarNames nestVarName name argTypes

    handleConstructor :: [Name] -> Name -> Name -> [Type] -> Q Clause
    handleConstructor extraTyVarNames nestVarName cName argTypes = do
      varNames <- replicateM (length argTypes) (newName "x")
      evalASTName <- newName "evalAST"
      handledArguments <-
        mapM
          ( \(argType, varName) ->
              handleConstructorArg True nestVarName evalASTName argType (VarE varName)
          )
          (zip argTypes varNames)
      return $
        Clause
          [ if any snd handledArguments
              then VarP evalASTName
              else WildP,
            ConP cName [] (map VarP varNames)
          ]
          ( NormalB $
              foldl
                (\f (x, _) -> AppE f x)
                (foldl (\e v -> AppTypeE e (VarT v)) (VarE . lowerFirst $ cName) extraTyVarNames)
                handledArguments
          )
          []

-- | Helper function for 'makeInterpretation'. This is a hairy one, so let me
-- explain:
--
-- Assume your effect type is defined by something like
--
-- > data Quux m a where
-- >   Quux :: Either (m a, IO x) [b -> m a] -> Quux m a
--
-- (The precise types don't matter, they're just there to illustrate the level
-- of complexity we might encounter.) Then, the "interpretation" instance takes
-- the form
--
-- > instance SomeConstraint m => InterpretEffect m Quux where
-- >   interpretEffect evalAST (Quux arg) = quux arg'
--
-- where @arg@ will be of type
--
-- > Either (AST ops a, IO x) [b -> AST ops a]
--
-- What this function accomplishes is generate the term @arg'@ of type
--
-- > Either (m a, IO a) [b -> m a]
--
-- (where @m@ is the "domain of interpretation" in the instance). Note that the
-- difference between these two types is just that @AST ops@ is replaced by
-- @m@. We can write @arg'@ given @arg@, because we have the function
--
-- > evalAST :: AST ops a -> m a
--
-- which allows us to transform every /positive/ occurrence of @AST ops a@ into
-- @m a@. (To see why negative positions don't work, assume we have @arg :: AST
-- ops a -> b@. Given only @evalAST@, we'll not be able to construct a function
-- of type @m a -> b@.)
handleConstructorArg ::
  -- | Are we in a positive position at the moment?
  Bool ->
  -- | 'Name' of the "nesting" monad in the effect type definition (this is
  -- the penultimate argument of the effect type, the one of kind @* -> *@).
  Name ->
  -- | 'Name' of the function @evalAST@ that evaluates "nested" 'AST's in effects
  Name ->
  -- | Type of the constructor argument we're currently handling
  Type ->
  -- | expression we're slowly building up while traversing the type
  Exp ->
  -- | final expression, together with a boolean that indicates whether we used
  -- @evalAST@
  Q (Exp, Bool)
--
-- If the type of the constructor argument is @m a@, where @m@ is the "nesting"
-- monad, we'll have to use @evalAST@. (But only in positive positions)
--
handleConstructorArg polarity nestName evalASTName (AppT (VarT x) _) expr
  | x == nestName =
      if polarity
        then (,True) <$> [e|$(varE evalASTName) $(return expr)|]
        else error "effect nesting in negative position"
--
-- If the type of the constructor argument of the form @l -> r@, we'll have to
-- pre- and post-compose with the correct functions in order to turn all @AST
-- ops a@ into @m a@. Luckily, we can compute these functions recursively from
-- the shapes of @l@ and @r@.
--
-- Note that we'll have to flip the polarity for the left side!
--
handleConstructorArg polarity nestName evalASTName (AppT (AppT ArrowT l) r) expr = do
  aName <- newName "a"
  (le, evalASTusedL) <- handleConstructorArg (not polarity) nestName evalASTName l (VarE aName)
  (re, evalASTusedR) <- handleConstructorArg polarity nestName evalASTName r (VarE aName)
  (,evalASTusedL || evalASTusedR)
    <$> [e|(\ $(varP aName) -> $(return re)) . $(return expr) . (\ $(varP aName) -> $(return le))|]
--
-- The trick to recursively compute the correct functions to apply to subtypes
-- and then combine them works for constructor arguments of the shapes @[...]@,
-- @Maybe ...@, @Either ... ...@, and @(..., ...)@.
--
-- The general pattern to note is that
--
-- - @[]@ and @Maybe@ are functors, so if we know how to transform a single
--   element, we can just use @fmap@
--
-- - @Either@ and @(,)@ are 'Bifunctor's, so we can use 'bimap'
--
-- - @->@ is also a bifunctor (in the category-theoretical sense), namely the
--   Hom-functor. The only difference to the other two bifunctors is the fact
--   that it is contravariant in its first argument, but the "pre- and
--   post-composition operation" /is/ its 'bimap'.
--
handleConstructorArg polarity nestName evalASTName (AppT ListT t) expr = do
  aName <- newName "a"
  (te, evalASTused) <- handleConstructorArg polarity nestName evalASTName t (VarE aName)
  (,evalASTused) <$> [e|map (\ $(varP aName) -> $(return te)) $(return expr)|]
handleConstructorArg polarity nestName evalASTName (AppT (ConT x) t) expr
  | x == ''Maybe = do
      aName <- newName "a"
      (te, evalASTused) <- handleConstructorArg polarity nestName evalASTName t (VarE aName)
      (,evalASTused) <$> [e|fmap (\ $(varP aName) -> $(return te)) $(return expr)|]
handleConstructorArg polarity nestName evalASTName (AppT (AppT x l) r) expr
  | x == ConT ''Either || x == TupleT 2 = do
      aName <- newName "a"
      (le, evalASTusedL) <- handleConstructorArg polarity nestName evalASTName l (VarE aName)
      (re, evalASTusedR) <- handleConstructorArg polarity nestName evalASTName r (VarE aName)
      (,evalASTusedL || evalASTusedR)
        <$> [e|bimap (\ $(varP aName) -> $(return le)) (\ $(varP aName) -> $(return re)) $(return expr)|]
--
-- If the type of the constructor argument is @IO a@, there's nothing to do.
-- Just keep it.
--
handleConstructorArg _polarity _nestName _evalASTName (AppT (ConT x) _) expr
  | x == ''IO = return (expr, False)
--
-- Parentheses can be ignored.
--
handleConstructorArg polarity nestName evalASTName (ParensT t) expr =
  handleConstructorArg polarity nestName evalASTName t expr
--
-- For a solidary type variable or type constructor there's nothing to do.
--
handleConstructorArg _ _ _ (VarT _) expr = return (expr, False)
handleConstructorArg _ _ _ (ConT _) expr = return (expr, False)
--
-- catchall for all types that we can't handle at the moment.
--
handleConstructorArg _ _ _ t _ = error $ "Effect argument type of this shape is not (yet) supported: " ++ show t

-- * Helper functions

-- | Transform a name so that the first letter is lower case.
lowerFirst :: Name -> Name
lowerFirst = mkName . lowerFirstString . nameBase
  where
    lowerFirstString (c : cs) = toLower c : cs
    lowerFirstString [] = error "empty name. This can't happen unless I wrote some very weird TemplateHaskell."

-- | Get the corresponding effect name for the name of a class. The naming
-- scheme is that @X@ will correspond to @XEffect@.
mkEffectName :: Name -> Name
mkEffectName = mkName . (++ "Effect") . nameBase

mapMaybeM :: (Monad m) => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM _ [] = return []
mapMaybeM f (x : xs) = do
  my <- f x
  case my of
    Nothing -> mapMaybeM f xs
    Just y -> (y :) <$> mapMaybeM f xs
