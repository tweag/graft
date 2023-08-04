{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

-- | A simple, but complete, tutorial for  how to use "Logic.Ltl". This does
-- not cover
--
-- - using higher-order effects in the LTL setting, and
--
-- - combining several different effects in one test scenario.
module Examples.Ltl.Simple where

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Effect
import Effect.Fail
import Effect.Fail.Passthrough ()
import Effect.TH
import Language.Haskell.TH (varT)
import Logic.Ltl

-- * Example domain and implementation

-- $doc
-- It's easiest to use this library if you have a type class of monads that
-- captures the behaviour you want to test. For the sake of this tutorial, let's
-- take a key-value-store.

class (MonadFail m) => MonadKeyValue k v m where
  storeValue :: k -> v -> m ()
  getValue :: k -> m (Maybe v)
  deleteValue :: k -> m ()

-- $doc
-- From this type class, we can write a few test cases,
-- corresponding to a serie of actions over key-value-store.

swapTrace :: (MonadKeyValue String Integer m) => m (Integer, Integer)
swapTrace = do
  storeValue "a" 1
  storeValue "b" 2
  Just a <- getValue @_ @Integer "a"
  Just b <- getValue @_ @Integer "b"
  storeValue "a" b
  storeValue "b" a
  Just a' <- getValue @_ @Integer "a"
  Just b' <- getValue @_ @Integer "b"
  return (a', b')

deleteTrace :: (MonadKeyValue String Integer m) => m Integer
deleteTrace = do
  storeValue "a" 1
  storeValue "b" 2
  deleteValue @_ @Integer "a"
  storeValue "a" 2
  Just a <- getValue @_ @Integer "a"
  return a

-- $doc
-- What we'll test is an implementation of 'MonadKeyValue'. We'll implement it
-- very simply, but note that the implementation of 'deleteValue' is wrong: we
-- never delete anything from the store. We'll "find" this mistake later on.

type KeyValueT k v = StateT (Map k v)

runKeyValueT :: Map k v -> KeyValueT k v m a -> m (a, Map k v)
runKeyValueT = flip runStateT

instance (Ord k, MonadFail m) => MonadKeyValue k v (KeyValueT k v m) where
  storeValue k v = modify $ Map.insert k v
  getValue k = gets $ Map.lookup k
  deleteValue _ = return ()

-- * Using the effect system

-- $doc
-- This library based on a custom effect system. The central type is @'AST' ops
-- a@. It describes abstract syntax trees of monadic computations which use
-- operations from the list @ops@ of /effect types/, and return an @a@. Such
-- 'AST's will be /interpreted/ in various ways to obtain interesting test
-- cases.
--
-- So, we'll have to write an effect type for the key-value store. The
-- constructors of that effect type will correspond to the methods of the
-- class 'MonadKeyValue'. We can think of them as abstract representations that
-- stand for the methods.
--
-- The kind of effect types is
--
-- > Effect = (Type -> Type) -> Type -> Type
--
-- The @(Type -> Type)@ parameter doesn't interest us here; it is the "nesting"
-- monad used for higher order effects. The second parameter is the return type
-- of the method.

data KeyValueEffect k v :: Effect where
  StoreValue :: k -> v -> KeyValueEffect k v m ()
  GetValue :: k -> KeyValueEffect k v m (Maybe v)
  DeleteValue :: k -> KeyValueEffect k v m ()

makeReification
  (\_ ops -> [t|(EffectInject FailEffect $(varT ops))|])
  ''MonadKeyValue
  ''KeyValueEffect

makeInterpretation
  (\_ _ -> [t|()|])
  ''MonadKeyValue
  ''KeyValueEffect

-- $doc
-- If the constructor names of 'KeyValueEffect' are the method names of
-- 'MonadKeyValue' (starting with an upper case letter) and the types match,
-- the Template Haskell macro 'makeEffect' can be used to generate two instance
-- definitions:
--
-- The "reification" instance
--
-- > instance (EffectInject (KeyValueEffect k v) ops) => MonadKeyValue k v (AST ops) where
--
-- says that, if @KeyValueEffect k v@ is an element of the list of effects
-- @ops@, then an 'AST' that uses the effect list @ops@ is an instance of
-- @MonadKeyValue k v@. This will allow us to write 'AST's using the familiar
-- syntax of 'MonadKeyValue'.
--
-- The "interpretation" instance
--
-- > instance (MonadKeyValue k v m) => InterpretEffect m (KeyValueEffect k v) where
--
-- says that the @KeyValueEffect k v@ can be interpreted into any
-- @MonadKeyValue k v@.
--
-- If you have to add extra constraints to the instances, you can use the more
-- flexible macros 'makeReification' and 'makeInterpretation'.
--
--
-- If all effects in an 'AST' have a suitable 'InterpretEffect' instance,
-- you'll be able to interpret the complete 'AST' with functions like
-- 'interpretAST'. So, what we've accomplished up to now is just as in any
-- other effect system: we have a single monad 'AST' that is parametrised on
-- the effect(s) you want to use, and an "interpetation" function that turns
-- the "staged" computations in 'AST's into actual computations in your domain
-- of interest.
--
-- At the very least, 'makeEffect' and friends will need the following language
-- extensions:
--
-- > {-# LANGUAGE ConstraintKinds #-}
-- > {-# LANGUAGE FlexibleContexts #-}
-- > {-# LANGUAGE FlexibleInstances #-}
-- > {-# LANGUAGE KindSignatures #-}
-- > {-# LANGUAGE MultiParamTypeClasses #-}
-- > {-# LANGUAGE TemplateHaskell #-}
--
-- For effect types with parameters (like @k@ and @v@ in 'KeyValueEffect',
-- you'll also need
--
-- > {-# LANGUAGE ScopedTypeVariables #-}
-- > {-# LANGUAGE TypeApplications #-}
--
-- There are scenarios where you might also need 'UndecidableInstances' but
-- we'll not discuss these here.

-- * Defining a type of single-step modifications

-- $doc
-- The module "Logic.Ltl" implements one way to turn the effect system into a
-- testing tool. Its idea is to change the interpretaion of an 'AST' by
-- applying single-step modifications to some actions it contains. A formula in an
-- LTL-like language determines when to apply the single-step modifications.
--
-- So, we first need a type of single-step modifications. These have no
-- intrinsic meaning, but will only be explained by the 'InterpretLtl'
-- instance.

data KeyValueMod k = KeyValueMod
  { toIgnoreOverride :: Bool,
    transformation :: k -> k
  }

renameKey :: (k -> k) -> KeyValueMod k
renameKey f = KeyValueMod {toIgnoreOverride = False, transformation = f}

noStoreOverride :: KeyValueMod k
noStoreOverride = KeyValueMod {toIgnoreOverride = True, transformation = id}

-- $doc
-- The evaluation of 'Ltl' formulas sometimes makes it necessary to try
-- applying two 'SingleStepMod's on the same step. The 'Semigroup' instance
-- describes how they should combine. (In our example, it's very simple,
-- because there is only one 'SingleStepMod', namely 'ConcatIfReplace'.)

-- TODO write something about commutativity
-- copy warning for LtlAnd

instance Semigroup (KeyValueMod k) where
  mod1 <> mod2 =
    KeyValueMod
      { toIgnoreOverride = toIgnoreOverride mod1 || toIgnoreOverride mod2,
        transformation = transformation mod1 . transformation mod2
      }

-- $doc
-- The 'InterpretLtl' instance is the heart of this while operation, since it
-- describes how we to apply 'SingleStepMod's to 'KeyValueEffect's. We
-- have to write a function
--
-- > interpretLtl :: KeyValueEffect k v dummy a -> SingleStepMod -> m (Maybe a)
--
-- which describes for each 'KeyValueEffect' if and how it is modified by each
-- modification. If the modification applies, it should return 'Just',
-- otherwise 'Nothing'. The @dummy@ type argument to 'KeyValueEffect' isn't
-- interesting to us here, it'll only be relevant for higer-order effects.
--
-- In our example, we make it so that the meaning of 'ConcatIfReplace' is: "If
-- you see a @'StoreValue' key value@ and there's already some @oldValue@ for
-- that @key@ in the store, don't just store @value@, store @oldValue <>
-- newValue@."
--
-- Note that this meaning of 'ConcatIfReplace' depends on the state of the
-- store. Herein lies a strength of this framework: what we're doing is really
-- more general than generating a list of 'AST's and evaluating them in a
-- second step. The parameters and applicability of the modification we apply
-- at the @n@-th step may depend on information we know only after having run
-- (and modified) the first @n-1@ steps.

instance (MonadKeyValue k v m) => InterpretLtl (KeyValueMod k) m (KeyValueEffect k v) where
  interpretLtl (StoreValue key nVal) = Apply $ \modif -> do
    val <- getValue @k @v key
    case (val, toIgnoreOverride modif) of
      (Just _, True) -> return (Just ())
      (Nothing, True) -> return Nothing
      (_, False) -> storeValue (transformation modif key) nVal >> return (Just ())
  interpretLtl (DeleteValue key) = Apply $ \modif ->
    if toIgnoreOverride modif
      then return Nothing
      else deleteValue @k @v (transformation modif key) >> return (Just ())
  interpretLtl (GetValue key) = Apply $ \modif ->
    if toIgnoreOverride modif
      then return Nothing
      else Just <$> getValue @k @v (transformation modif key)

-- * Interpreting modified 'AST's

-- $doc
--
-- The module "Logic.Ltl" provides the wrapper type @'LtlAST' mod ops@, which
-- is an 'AST' in which you'll have access to the function
--
-- > modifyLtl :: Ltl mod -> LtlAST mod ops a -> LtlAST mod ops a
--
-- This is what makes it possible to deploy composite 'Ltl' modifications: wrap
-- the part of the computation you want to modify in 'modifyLtl' with the 'Ltl'
-- formula of your choice.
--
-- The module also provides
-- - All of the effects in @ops@ have an 'InterpretLtl mod m' instance (this is
--   the 'InterpretEffectsLtl' constraint).
--
-- - @m@ is a 'MonadPlus'. This is necessary because there might be several
--   ways to satisfy an 'Ltl' formula. The whole point of using 'Ltl' do describe
--   modifications of a single trace is to try /all/ of the possible ways to
--   apply the formula.
--
-- Using 'interpretLtlAST', we can write a convenience function that will
-- interpret an 'LtlAST' of 'KeyValueEffect's and return the final return value
-- and state of the store:

interpretAndRun ::
  (Ord k, InterpretLtl (KeyValueMod k) (KeyValueT k v []) (KeyValueEffect k v)) =>
  Map k v ->
  LtlAST (KeyValueMod k) '[KeyValueEffect k v, FailEffect] a ->
  [(a, Map k v)]
interpretAndRun initialState acts = runKeyValueT initialState $ interpretLtlAST @'[InterpretLtlTag, InterpretEffectStatefulTag] acts

-- * A few example traces

-- ** 'somewhere' and 'everywhere'

-- $doc
-- By for the most commonly used 'Ltl' formula is 'somewhere'. The 'LtlAST'
-- describes the three traces you get by applying @x@ to @act1@, @act2@, and
-- @act3@, while leaving the other actions unmodified. Only traces where @x@
-- was /successfully/ applied will be returned by 'interpretLTLAST', though. This means
-- that our first example will return an empty list, since 'ConcatIfReplace'
-- never applies (as we never 'storeValue' for a key that's already present).
--
-- >>> exampleSomewhereSwap
-- [((1,1),fromList [("a",1),("anew",2),("b",1)]),((2,2),fromList [("a",2),("b",2),("bnew",1)])]

appendNew :: KeyValueMod String
appendNew = renameKey (++ "new")

exampleSomewhereSwap :: [((Integer, Integer), Map String Integer)]
exampleSomewhereSwap =
  interpretAndRun mempty $
    modifyLtl (somewhere noStoreOverride) swapTrace

-- $doc
-- In the next example, we'll expect two results, because there are two
-- positions in which 'ConcatIfReplace' applies, namely the second and third
-- 'storeValue'. Let's explain the two results:
--
-- - If we apply 'ConcatIfReplace' to the second 'storeValue', the store will
--   hold @\"Hello\"@ for key @1@, so we'll store @\"Hello my\"@. However, this is
--   invisible in the result, because the third 'storeValue' will overwrite this
--   with "friend".
--
-- - If we apply 'ConcatIfReplace' to the third 'storeValue', the store will hold
--   @\"my\"@ at key @1@, so we'll store @\"my friend\"@. Since there are no more
--   'storeValue' operations after that, that's also what we see in the result.
--
-- >>> exampleSomewhereDelete
-- [(2,fromList [("a",2),("anew",1),("b",2)]),(2,fromList [("a",2),("bnew",2)]),(2,fromList [("a",2),("b",2)]),(1,fromList [("a",1),("anew",2),("b",2)])]

exampleSomewhereDelete :: [(Integer, Map String Integer)]
exampleSomewhereDelete =
  interpretAndRun mempty $
    modifyLtl (somewhere noStoreOverride) deleteTrace

-- $doc
-- Another very commonly used 'Ltl' formula is 'everywhere'. It applies the
-- given single-step modification to every action in the 'AST'.
--
-- This means that our next example will again return the empty list, since
-- 'ConcatIfReplace' isn't applicable on the first 'storeValue'.
--
-- >>> exampleEverywhereCorrect
-- [(1,2)]

exampleEverywhereCorrect :: [(Integer, Integer)]
exampleEverywhereCorrect =
  fst <$> interpretAndRun mempty (modifyLtl (everywhere noStoreOverride) swapTrace)

-- $doc
--
-- >>> exampleEverywhereBug
-- [1]

exampleEverywhereBug :: [Integer]
exampleEverywhereBug =
  fst <$> interpretAndRun mempty (modifyLtl (everywhere noStoreOverride) deleteTrace)

-- $doc
-- Note that, unlike 'somewhere', 'everywhere' doesn't imply that any
-- modification is applied. Applying 'everywhere' to an empty trace is
-- successful, and returns one result:
--
-- >>> exampleEverywhereEmpty
-- [((),fromList [])]

exampleEverywhereEmpty :: [((), Map String Integer)]
exampleEverywhereEmpty =
  interpretAndRun mempty $
    modifyLtl (everywhere appendNew) $
      return ()

-- ** 'there'

-- $doc
-- We can make the modification applicable, and return the expected @"Hello my
-- friend"@ at key @1@, if we only apply 'everywhere' after the first action:
-- This requires a custom formula using @'LtlNext' which starts on next step.
--
-- >>> exampleThereEmpty
-- []

exampleThereEmpty :: [Integer]
exampleThereEmpty =
  fst <$> interpretAndRun mempty (modifyLtl (there 4 appendNew) deleteTrace)

-- >>> exampleThereBug
-- [1]

exampleThereBug :: [Integer]
exampleThereBug =
  fst <$> interpretAndRun mempty (modifyLtl (there 3 noStoreOverride) deleteTrace)

-- ** Custom 'Ltl' formulas

-- $doc
-- There are many possibilities for custom formulas. Please refer to the
-- documentation
-- of 'Ltl'.
