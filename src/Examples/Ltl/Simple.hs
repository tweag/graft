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
import Effect.Fail
import Effect.Fail.Passthrough ()
import Effect.TH
import Logic.Ltl

-- * Example domain and implementation

-- $doc
-- To use this library, you need a type class of monads that captures
-- the behaviour you want to test. For the sake of this tutorial,
-- let's take a key-value-store.

class (MonadFail m) => MonadKeyValue k v m where
  storeValue :: k -> v -> m ()
  getValue :: k -> m (Maybe v)
  deleteValue :: k -> m ()

-- $doc
-- From this type class, we can write a few test cases, corresponding
-- to a serie of actions over key-value-store.

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
-- What we'll test is an implementation of 'MonadKeyValue'. We'll
-- implement it very simply, but note that the implementation of
-- 'deleteValue' is wrong: we never delete anything from the
-- store. We'll "find" this mistake later on.

type KeyValueT k v = StateT (Map k v)

runKeyValueT :: Map k v -> KeyValueT k v m a -> m (a, Map k v)
runKeyValueT = flip runStateT

instance (Ord k, MonadFail m) => MonadKeyValue k v (KeyValueT k v m) where
  storeValue k v = modify $ Map.insert k v
  getValue k = gets $ Map.lookup k
  deleteValue _ = return ()

-- * Using the effect system

-- $doc
-- This library based on a custom effect system. There's a macro that
-- will write such an effect type for us, and give it the name
-- @MonadKeyValueEffect@:

defineEffectType ''MonadKeyValue

-- $doc
-- Now, we have to make the rest of the machinery aware that we want
-- to use the effect type we just defined as the abtract
-- representation for @MonadKeyValue@:

makeEffect ''MonadKeyValue ''MonadKeyValueEffect

-- * Defining a type of single-step modifications

-- $doc
-- The testing method provided by this library consists in applying
-- single steps modifications to abstract representations of the
-- domain (the effects). These modifications can then be deployed at
-- various steps in traces of actions.
--
-- So, we first need a type of single-step modifications. These have
-- no intrinsic meaning, as a semantics will be given through means of
-- interpreting them over the domain actions. However, their name and
-- type can give hints as to how they will be interpreted later on.
--
-- Here we propose a type of modification which will both render
-- possible to ignore stores when overriding an existing value, and to
-- rename a key in various operations.

data KeyValueMod k = KeyValueMod
  { toIgnoreOverride :: Bool,
    transformation :: k -> k
  }

-- $doc
-- We propose two smart constructors, one for creating a modification
-- that transforms names solely, the other that only ignore overrides.

renameKey :: (k -> k) -> KeyValueMod k
renameKey f = KeyValueMod {toIgnoreOverride = False, transformation = f}

noStoreOverride :: KeyValueMod k
noStoreOverride = KeyValueMod {toIgnoreOverride = True, transformation = id}

-- * Using Logic.Ltl to deploy single step in time

-- $doc
-- The module "Logic.Ltl" implements one way to turn the effect system
-- into a testing tool by deploying single step modification in
-- time. A formula in an LTL-like language determines when to apply
-- the single-step modifications.
--
-- The evaluation of 'Ltl' formulas sometimes makes it necessary to
-- try applying two 'SingleStepMod's on the same step. The 'Semigroup'
-- instance describes how they should combine. Note that this
-- combination will not necessarily be commutative.
--
-- In our example, this instance is straighforward. If one of the two
-- requires to ignore override, then the result will as well. In
-- addition, modifications over key will be functionally composed.

instance Semigroup (KeyValueMod k) where
  mod1 <> mod2 =
    KeyValueMod
      { toIgnoreOverride = toIgnoreOverride mod1 || toIgnoreOverride mod2,
        transformation = transformation mod1 . transformation mod2
      }

-- $doc
-- The 'InterpretLtl' instance is the heart of this whole operation,
-- since it describes how we to apply our single steps modifications
-- to our effects.  Thanks to our @defineEffectType macro, we have
-- access to abstract representation of actions, which are their
-- capitalized versions on which we can case split.  This function
-- will return @Nothing whenever the modification fails (does not
-- apply).
--
-- In our case, we apply the transformation whenever required, and
-- replace stores with noOp when required.

instance (MonadKeyValue k v m) => InterpretLtl (KeyValueMod k) m (MonadKeyValueEffect k v) where
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
--
-- > interpretLtlAST :: forall mod m ops a. (Semigroup mod, MonadPlus m, InterpretEffectsLtl mod m tags ops) => LtlAST mod ops a -> m a
--
-- which interprets the @'LtlAST' mod ops@ into any suitable monad @m@. Here,
-- "suitable" means:
--
-- - All of the effects in @ops@ have one of the following three instances:
--
--     - @InterpretLtl mod m@ (this is what we have here)
--
--     - @InterpretLtlHigherOrder mod m@ (this is for higher order effect
--       types, we're not interested in that here)
--
--     - @InterpretEffectStateful (Const [Ltl mod]) m@ (this is a low-level
--       class used to implement the LTL framework itself, and we're /not at all/
--       interested in it here)
--
-- - @m@ is a 'MonadPlus'. This is necessary because there might be several
--   ways to satisfy an 'Ltl' formula. The whole point of using 'Ltl' do describe
--   modifications of a single trace is to try /all/ of the possible ways to
--   apply the formula.
--
-- Using 'interpretLtlAST', we can write a convenience function that will
-- interpret an 'LtlAST' of 'MonadKeyValueEffect's and return the final return value
-- and state of the store:
--
-- Note how we type-apply 'interpretLtlAST' to alist of "tags" of kind
-- 'LtlInstanceKind': These tags speficy, in order, which of the three
-- instances described above we expect the effects to have.

interpretAndRun ::
  (Ord k, InterpretLtl (KeyValueMod k) (KeyValueT k v []) (MonadKeyValueEffect k v)) =>
  Ltl (KeyValueMod k) ->
  LtlAST (KeyValueMod k) '[MonadKeyValueEffect k v, MonadFailEffect] a ->
  [(a, Map k v)]
interpretAndRun formula =
  runKeyValueT mempty . interpretLtlAST @'[InterpretLtlTag, InterpretEffectStatefulTag] . modifyLtl formula

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
  interpretAndRun (somewhere noStoreOverride) swapTrace

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
  interpretAndRun (somewhere noStoreOverride) deleteTrace

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
  fst <$> interpretAndRun (everywhere noStoreOverride) swapTrace

-- $doc
--
-- >>> exampleEverywhereBug
-- [1]

exampleEverywhereBug :: [Integer]
exampleEverywhereBug =
  fst <$> interpretAndRun (everywhere noStoreOverride) deleteTrace

-- $doc
-- Note that, unlike 'somewhere', 'everywhere' doesn't imply that any
-- modification is applied. Applying 'everywhere' to an empty trace is
-- successful, and returns one result:
--
-- >>> exampleEverywhereEmpty
-- [((),fromList [])]

exampleEverywhereEmpty :: [((), Map String Integer)]
exampleEverywhereEmpty =
  interpretAndRun (everywhere appendNew) (return ())

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
  fst <$> interpretAndRun (there 4 appendNew) deleteTrace

-- >>> exampleThereBug
-- [1]

exampleThereBug :: [Integer]
exampleThereBug =
  fst <$> interpretAndRun (there 3 noStoreOverride) deleteTrace

-- ** Custom 'Ltl' formulas

-- $doc
-- There are many possibilities for custom formulas. Please refer to the
-- documentation
-- of 'Ltl'.
