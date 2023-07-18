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

-- | A simple, but complete, tutorial for  how to use "Logic.Ltl". This does
-- not cover using higher-order effects in the LTL setting.
module Examples.Ltl.Simple where

import Control.Monad.State
-- the effect system that the testing framework is based on
-- Template Haskell helpers for the effect system
-- The "LTL" testing module

import Data.Kind (Type)
import Data.Map (Map)
import qualified Data.Map as Map
import Effect
import Effect.TH
import GHC.ExecutionStack (Location (functionName))
import GHC.IO.Handle (isEOF)
import GHC.Num (integerComplement)
import GHC.RTS.Flags (CCFlags (doCostCentres))
import Logic.Ltl

-- * Example domain and implementation

-- $doc
-- It's easiest to use this library if you have a type class of monads that
-- captures the behaviour you want to test. For the sake of this example, let's
-- take a key-value-store.

class (Monad m) => MonadKeyValue k v m where
  storeValue :: k -> v -> m ()
  getValue :: k -> m (Maybe v)
  deleteValue :: k -> m ()

-- $doc
-- What we'll test is the implementation of 'MonadKeyValue'. We'll implement it
-- very simply, but note that the implementation of 'deleteValue' is wrong:it
-- never deletes anything from the map. We'll try to "find" this mistake later
-- on.

type KeyValueT k v = StateT (Map k v)

runKeyValueT :: Map k v -> KeyValueT k v m a -> m (a, Map k v)
runKeyValueT = flip runStateT

instance (Ord k, Monad m) => MonadKeyValue k v (KeyValueT k v m) where
  storeValue k v = modify $ Map.insert k v
  getValue k = gets $ Map.lookup k
  deleteValue _ = return ()

-- * Using the effect system

-- $doc
-- This library based on a higher-order effect system. The central type is
--
-- > AST ops a
--
-- It describes abstract syntax trees of monadic computations which use
-- operations from the type-level list @ops@ of /effect types/, and return an
-- @a@. Such 'AST's will be /interpreted/ in various ways to obtain interesting
-- test cases.
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

makeEffect ''MonadKeyValue ''KeyValueEffect

-- $doc
-- If
--
-- - the constructor names of 'KeyValueEffect' are precisely the method names
--   of 'MonadKeyValue', just starting with an upper case letter, and
--
-- - the types of the constructor's arguments match the types of the method's
--   arguments,
--
-- the Template Haskell macro above will expand into two instance definitions:
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
-- If all effects in an 'AST' have a suitable 'InterpretEffect' instance,
-- you'll be able to interpret the complete 'AST' with functions like
-- 'interpretAST'.

-- * Defining a type of single-step modifications

-- $doc
-- The module "Logic.Ltl" turns the effect system into a testing tool. Its
-- idea is to apply single-step  modifications to actions in an 'AST' while
-- interpreting it. A formula in an LTL-like language determines when to apply
-- the single-step modifications.
--
-- So, we first need a type of single-step modifications. These have no
-- intrinsic meaning, but are only explained by the 'InterpretLtl' instance.

data SingleStepMod = ConcatIfReplace

-- $doc
-- The evaluation of 'Ltl' formulas sometimes makes it necessary to try
-- applying two 'SingleStepMod's on the same step. The 'Semigroup' instance
-- describes how they should combine. (In our example, it's very simple,
-- because there is only one 'SingleStepMod', namely 'ConcatIfReplace'.)

instance Semigroup SingleStepMod where
  a <> _ = a

-- $doc
-- The 'InterpretLtl' instance is the heart of this while operation, since it
-- describes how we to apply 'SingleStepMod's to 'KeyValueEffect's. We
-- have to implement a function
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

instance (Semigroup v, MonadKeyValue k v m) => InterpretLtl SingleStepMod m (KeyValueEffect k v) where
  interpretLtl (StoreValue key val) ConcatIfReplace = do
    -- the type application is needed here to get around the otherwise
    -- ambiguous type @v@:
    mv <- getValue @k @v key
    case mv of
      Just oldVal -> storeValue key (oldVal <> val) >> return (Just ())
      Nothing -> return Nothing
  interpretLtl _ _ = return Nothing

-- * Running a few examples

-- $doc
--
-- As a convenience wrapper, "Logic.Ltl" provides the type @'LtlAST' mod ops@,
-- which is like @'AST' mod ops@, only that in it, you'll have access to the
-- function
--
-- > modifyLtl :: Ltl mod -> LtlAST mod ops -> LtlAST mod ops
--
-- which is what makes it possible to deploy composite 'Ltl' modifications:
-- simply wrap the computation you want to modify in 'modifyLtl' with the 'Ltl'
-- formula of your choice.

interpretAndRun ::
  (Monoid v, Ord k) =>
  Map k v ->
  LtlAST SingleStepMod '[KeyValueEffect k v] a ->
  [(a, Map k v)]
interpretAndRun initialState acts = runKeyValueT initialState $ interpretLtlAST acts

example1 :: [((), Map Int String)]
example1 =
  interpretAndRun mempty $
    modifyLtl (somewhere ConcatIfReplace) $
      do
        storeValue 1 "Hello "
        storeValue 1 "my "
        storeValue 1 "friend"

example2 :: [((), Map Int String)]
example2 =
  interpretAndRun mempty $
    modifyLtl (everywhere ConcatIfReplace) $
      do
        storeValue 1 "Hello "
        storeValue 1 "my "
        storeValue 1 "friend"

example3 :: [((), Map Int String)]
example3 =
  interpretAndRun mempty $
    modifyLtl (LtlNext $ everywhere ConcatIfReplace) $
      do
        storeValue 1 "Hello "
        storeValue 1 "my "
        storeValue 1 "friend"

example4 :: [((), Map Int String)]
example4 =
  interpretAndRun mempty $
    modifyLtl (LtlNext $ everywhere ConcatIfReplace) $
      do
        storeValue 1 "Hello "
        storeValue 2 "my "
        storeValue 3 "friend"
