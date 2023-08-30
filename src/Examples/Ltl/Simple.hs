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
-- not cover
--
-- - using higher-order effects in the LTL setting, and
--
-- - combining several different effects in one test scenario.
--
-- If you're reading the Haddock documentation, consider reading the source,
-- it'll make more sense.
module Examples.Ltl.Simple where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Effect.Error
import Effect.Error.Passthrough ()
import Effect.TH
import Logic.Ltl
import Logic.SingleStep

-- * Example domain specification

-- $doc
-- To use this library, you need a type class of monads that captures the
-- behaviour you want to test. For the sake of this tutorial, let's take a
-- key-value-store where the keys are 'String's and the values are 'Integer's.

class (Monad m) => MonadKeyValue m where
  storeValue :: String -> Integer -> m ()
  getValue :: String -> m Integer
  deleteValue :: String -> m ()

-- $doc
-- We'll assume a number of /traces/ written using this type class. These will
-- most likely be manually written test cases that cover (some part of) the
-- normal usage of the system you're testing.
--
-- Here, we'll only write two slightly silly examples. The more different
-- scenarios you cover in these "seed" traces, the more interesting variations
-- will be generated later on.

swapTrace :: (MonadKeyValue m) => m (Integer, Integer)
swapTrace = do
  storeValue "a" 1
  storeValue "b" 2
  a <- getValue "a"
  b <- getValue "b"
  storeValue "a" b
  storeValue "b" a
  a' <- getValue "a"
  b' <- getValue "b"
  return (a', b')

deleteTrace :: (MonadKeyValue m) => m Integer
deleteTrace = do
  storeValue "a" 1
  storeValue "b" 2
  deleteValue "a"
  storeValue "a" 2
  getValue "a"

-- $doc
-- What we'll test is an implementation of 'MonadKeyValue'. We'll
-- implement it very simply, but note that the implementation of
-- 'deleteValue' is wrong: we never delete anything from the
-- store. We'll "find" this mistake later on.

newtype KeyValueError = NoSuchKey String deriving (Show)

type KeyValueT m = ExceptT KeyValueError (StateT (Map String Integer) m)

runKeyValueT :: Map String Integer -> KeyValueT m a -> m (Either KeyValueError a, Map String Integer)
runKeyValueT s0 = flip runStateT s0 . runExceptT

instance (Monad m) => MonadKeyValue (KeyValueT m) where
  storeValue k v = modify $ Map.insert k v
  getValue k = do
    m <- get
    case Map.lookup k m of
      Nothing -> throwError $ NoSuchKey k
      Just v -> return v
  deleteValue _ = return ()

-- * Using the effect system

-- $doc
-- This library is based on a custom effect system. There are a few macros that
-- will make using it more convenient. You'll at least need the following
-- language extensions (more extensions might be needed in more complex
-- scenarios than this tutorial):
--
-- > {-# LANGUAGE ConstraintKinds #-}
-- > {-# LANGUAGE FlexibleContexts #-}
-- > {-# LANGUAGE FlexibleInstances #-}
-- > {-# LANGUAGE KindSignatures #-}
-- > {-# LANGUAGE MultiParamTypeClasses #-}
-- > {-# LANGUAGE ScopedTypeVariables #-}
-- > {-# LANGUAGE TemplateHaskell #-}
-- > {-# LANGUAGE TypeApplications #-}
--
-- The first macro will write an /effect type/ corresponding to 'MonadKeyValue'
-- for us, and give it the name 'MonadKeyValueEffect':

defineEffectType ''MonadKeyValue

-- $doc
-- The type 'MonadKeyValueEffect' is an abstract representation of the class
-- 'MonadKeyValue'. This means that for each method of the class, there's a
-- constructor of the effect type:
--
-- - for @storeValue :: String -> Integer -> m ()@, there is @StoreValue :: String -> Integer -> MonadKeyValueEffect m ()@,
--
-- - for @getValue :: String -> m Integer@, there is @GetValue :: String -> MonadKeyValueEffect m Integer@, and
--
-- - for @deleteValue :: String -> m ()@, there is @DeleteValue :: String -> MonadKeyValueEffect m ()@.
--
-- We thus have a reification of computations in 'MonadKeyValue'. This
-- reification will be used to build 'AST's, which can then be interpreted in
-- flexible ways.
--
-- There's also a macro to define some instances that will make this
-- convenient.

makeEffect ''MonadKeyValue ''MonadKeyValueEffect

-- * Defining a type of single-step modifications

-- $doc
-- The testing method explained in this tutorial consists in deploying
-- single-step modifications while interpreting an 'AST'. The 'AST' will be
-- built from abstract representations of actions (i.e. the constructors of
-- effect types like 'MonadKeyValueEffect'), and we'll interpret it into some
-- suitable monad (here, that'll be @KeyValueT m@).
--
-- So, we'll first have to define a type of single-step modifications, and
-- explain how they should change the interpretation of actions. The
-- single-step modifications have no meaning in and of them themselves, as they
-- are only explained by how they apply to the constructors of
-- 'MonadKeyValueEffect'.

data KeyValueMod = KeyValueMod
  { noOverwrite :: Bool,
    renameKey :: String -> String
  }

-- $doc
-- Our modification type 'KeyValueMod' captures two behaviours:
--
-- - When 'noOverwrite' is @True@, the intended meaning is that
--   'storeValue' should be ignored when it replaces the value (i.e., when the
--   key is already present in the store)
--
-- - 'renameKey' will change the keys used by any action with a prescribed
--   function.
--
-- The 'InterpretMod' instance now makes these intended meanings explicit. The
-- function 'interpretMod' describes, for each constructor of
-- 'MonadKeyValueEffect', how it should be interpreted under a modification:
--
-- - Whenever the there's a modification that might apply, we'll try to apply
--   it using the 'Apply' constructor.
--
--   - When the modification applies, we signal that success by wrapping the
--     return value of the action in a 'Just'.
--
--   - When the modification doesn't apply, we return 'Nothing'.
--
-- - Whenever there's no modification, we have nothing to apply, so we return
--   'DontApply'. This will mean that the operation will be performed as usual.
--
-- - A third possibility, which is not shown here, is returning 'Ignore'
--   instead of 'Apply' or 'DontApply', which would mean to do the operation
--   without modification as usual, but remember the modification for the next
--   step. This is called "ignoring" the operation, because it makes the
--   operation invisible to modifications.

instance (MonadError KeyValueError m, MonadKeyValue m) => InterpretMod KeyValueMod m MonadKeyValueEffect where
  interpretMod (StoreValue key val) (Just modif) = Apply $ do
    oldVal <- catchError (Just <$> getValue key) (\NoSuchKey {} -> return Nothing)
    case (oldVal, noOverwrite modif) of
      (Just _, True) -> return (Just ())
      (Nothing, True) -> return Nothing
      (_, False) -> Just <$> storeValue (renameKey modif key) val
  interpretMod (DeleteValue key) (Just modif) =
    Apply $
      if noOverwrite modif
        then return Nothing
        else Just <$> deleteValue (renameKey modif key)
  interpretMod (GetValue key) (Just modif) =
    Apply $
      if noOverwrite modif
        then return Nothing
        else Just <$> getValue (renameKey modif key)
  interpretMod _ Nothing = DontApply

-- $doc
-- Here are two smart constructors for modifications, one for creating a
-- modification that transforms keys solely, the other that only ignores
-- overwrites:

renameKeys :: (String -> String) -> KeyValueMod
renameKeys f = KeyValueMod {noOverwrite = False, renameKey = f}

noStoreOverride :: KeyValueMod
noStoreOverride = KeyValueMod {noOverwrite = True, renameKey = id}

-- * Using "Logic.Ltl" to deploy single-step modifications

-- $doc
-- The module "Logic.Ltl" implements one way to combine single-step
-- modifications into composite modifications that apply to traces: a formula
-- in an LTL-like language determines when to apply the single-step
-- modifications.
--
-- The evaluation of such 'Ltl' formulas sometimes makes it necessary to try
-- applying two single-step modifications on the same step. The 'Semigroup'
-- instance describes how they should combine.

instance Semigroup KeyValueMod where
  mod1 <> mod2 =
    KeyValueMod
      { noOverwrite = noOverwrite mod1 || noOverwrite mod2,
        renameKey = renameKey mod1 . renameKey mod2
      }

-- $doc
-- The module "Logic.Ltl" provides the wrapper type @'LtlAST' mod ops@.
-- Here, @ops@ is the list of effect types related to our domain. In our case,
-- it will have to contain 'MonadKeyValueEffect' and @MonadErrorEffect
-- KeyValueError@. The Template Haskell macros we used above make it so that
--
-- > LtlAST mod '[MonadKeyValueEffect, MonadErrorEffect KeyValueError]
--
-- is an instance of 'MonadKeyValue' and @MonadError KeyValueError@. The
-- parameter @mod@ is the type of single-step modifications; here it is
-- 'KeyValueMod'.
--
-- In addition to all the 'MonadKeyValue' and 'MonadError' functions, the
-- 'LtlAST' also gives you access to the function
--
-- > modifyLtl :: Ltl mod -> LtlAST mod ops a -> LtlAST mod ops a
--
-- This is what makes it possible to deploy composite 'Ltl' modifications: wrap
-- the part of the computation you want to modify in 'modifyLtl' with the 'Ltl'
-- formula of your choice.
--
-- The module "Logic.Ltl" also provides
--
-- > interpretLtlAST :: forall mod m ops a. (Semigroup mod, MonadPlus m, InterpretEffectsLtl mod m tags ops) => LtlAST mod ops a -> m a
--
-- which interprets the @'LtlAST' mod ops@ into any suitable monad @m@. Here,
-- "suitable" means:
--
-- - All of the effects in @ops@ have one of the following three instances:
--
--     - @InterpretMod mod m@ (this is what we have here)
--
--     - @InterpretLtlHigherOrder mod m@ (this is for higher order effect
--       types, we're not interested in that here)
--
--     - @InterpretEffectStateful (Const [Ltl mod]) m@ (this is a low-level
--       class used to implement the LTL framework itself)
--
-- - @m@ is a 'MonadPlus'. This is necessary because there might be several
--   ways to satisfy an 'Ltl' formula. The whole point of using 'Ltl' do describe
--   modifications of a single trace is to try /all/ of the possible ways to
--   apply the formula. Sometimes, this requires defining a custom 'MonadPlus'
--   instance for the monad (or transformer) we're interested in.

instance {-# OVERLAPPING #-} (MonadPlus m) => Alternative (KeyValueT m) where
  empty = lift $ lift mzero
  ExceptT (StateT a) <|> (ExceptT (StateT b)) = ExceptT $ StateT $ \x -> a x `mplus` b x

instance {-# OVERLAPPING #-} (MonadPlus m) => MonadPlus (KeyValueT m)

-- $doc
-- Using 'interpretLtlAST', we can write a convenience function that will
-- interpret an 'LtlAST' of 'MonadKeyValueEffect's and return the final return value
-- and state of the store.
--
-- Note how we type-apply 'interpretLtlAST' to a list of "tags" of kind
-- 'LtlInstanceKind': These tags specify, in order, which of the three
-- instances described above we expect the effects to have.
--
-- The 'InterpretEffectStateful' instance for 'MonadErrorEffect' is imported
-- from "Effect.Error.Passthrough", and is implemented in a generic way so as
-- to ignore every modification: we only care about modifying 'MonadKeyValue'
-- actions.

interpretAndRun ::
  LtlAST KeyValueMod '[MonadKeyValueEffect, MonadErrorEffect KeyValueError] a ->
  [(Either KeyValueError a, Map String Integer)]
interpretAndRun =
  runKeyValueT mempty
    . interpretLtlAST
      @'[ InterpretModTag,
          InterpretEffectStatefulTag
        ]

-- * A few examples

-- ** 'somewhere'

-- $doc
-- By far the most commonly used 'Ltl' formula is 'somewhere'.
--
-- In our first example, we try applying the modification 'noStoreOverride' to
-- some action in the 'swapTrace'. There are two actions where the modification
-- applies, namely the third and fourth 'storeValue's:
--
-- > swapTrace = do
-- >   storeValue "a" 1
-- >   storeValue "b" 2
-- >   a <- getValue "a"
-- >   b <- getValue "b"
-- >   storeValue "a" b   -- replaced by no-op in branch 1
-- >   storeValue "b" a   -- replaced by no-op in branch 2
-- >   a' <- getValue "a"
-- >   b' <- getValue "b"
--
-- So, we expect to have two modified traces, where both "a" and "b" share the
-- same value, and that's indeed the case:
--
-- >>> exampleSomewhereSwap
-- [(Right (1,1),fromList [("a",1),("b",1)]),
--  (Right (2,2),fromList [("a",2),("b",2)])]

exampleSomewhereSwap :: [(Either KeyValueError (Integer, Integer), Map String Integer)]
exampleSomewhereSwap = interpretAndRun $ modifyLtl (somewhere noStoreOverride) swapTrace

-- $doc
-- In the 'deleteTrace', we expect 'noStoreOverride' never to apply as
-- there should be no override. However, it applies because our
-- implementation of 'deleteKey' does not actually delete anything.
--
-- > deleteTrace = do
-- >   storeValue "a" 1
-- >   storeValue "b" 2
-- >   deleteValue "a"
-- >   storeValue "a" 2 -- replaced by no-op
-- >   getValue "a"
--
-- We have "discovered" the bug!
--
-- >>> exampleSomewhereDelete
-- [(Right 1,fromList [("a",1),("b",2)])]

exampleSomewhereDelete :: [(Either KeyValueError Integer, Map String Integer)]
exampleSomewhereDelete =
  interpretAndRun $ modifyLtl (somewhere noStoreOverride) deleteTrace

-- ** 'everywhere'

-- $doc
-- Another very commonly used 'Ltl' formula is 'everywhere'. It must
-- apply the given single-step modification to every action in the
-- 'AST'. If it is not applicable somewhere, then there will be no
-- output trace.
--
-- So, when we apply @everywhere noStoreOverride@ to the swapTrace, we'll get
-- no results, because not all 'storeValue's in that trace replace the value at
-- a key.
--
-- >>> exampleEverywhereSwap
-- []

exampleEverywhereSwap :: [(Either KeyValueError (Integer, Integer), Map String Integer)]
exampleEverywhereSwap =
  interpretAndRun $ modifyLtl (everywhere noStoreOverride) swapTrace

-- $doc
-- On the other hand, 'renameKeys' always applies, and hence we can
-- successfully apply it to, say the 'deleteTrace', and thus prove that its
-- behaviour is independent under renaming of keys.
--
-- >>> exampleEverywhereDelete
-- [(Right 2,fromList [("anew",2),("bnew",2)])]

exampleEverywhereDelete :: [(Either KeyValueError Integer, Map String Integer)]
exampleEverywhereDelete =
  interpretAndRun $ modifyLtl (everywhere $ renameKeys (++ "new")) deleteTrace

-- $doc
-- Note that, unlike 'somewhere', 'everywhere' doesn't imply that any
-- modification is applied. Applying 'everywhere' to an empty trace is
-- successful, and returns one result:
--
-- >>> exampleEverywhereEmpty
-- [((),fromList [])]

exampleEverywhereEmpty :: [(Either KeyValueError (), Map String Integer)]
exampleEverywhereEmpty =
  interpretAndRun $ modifyLtl (everywhere noStoreOverride) (return ())

-- ** 'there'

-- $doc
-- In addition to 'somewhere' and 'everywhere', it is also possible to
-- require the application of a modification starting from a specific position in
-- a trace using 'there'
--
-- >>> exampleThere
-- [(Right (),fromList [("a",1),("b",2),("cnew",3),("d",4)]),
--  (Right (),fromList [("a",1),("b",2),("c",3),("dnew",4)])]

exampleThere :: [(Either KeyValueError (), Map String Integer)]
exampleThere =
  interpretAndRun $ modifyLtl (there 2 $ somewhere $ renameKeys (++ "new")) $ do
    storeValue "a" 1
    storeValue "b" 2
    storeValue "c" 3
    storeValue "d" 4

-- $doc
-- Another idiom to accomplish the same without using 'there' is to only apply
-- 'modifyLtl' after the first few actions:
--
-- >>> exampleNotThere
-- [(Right (),fromList [("a",1),("b",2),("cnew",3),("d",4)]),
--  (Right (),fromList [("a",1),("b",2),("c",3),("dnew",4)])]

exampleNotThere :: [(Either KeyValueError (), Map String Integer)]
exampleNotThere =
  interpretAndRun $ do
    storeValue "a" 1
    storeValue "b" 2
    modifyLtl (somewhere $ renameKeys (++ "new")) $ do
      storeValue "c" 3
      storeValue "d" 4

-- ** Custom 'Ltl' formulas

-- $doc
-- Finally, it is possible to create formulas by hand using the 'Ltl'
-- constructors. In this example, we add "new" to the key of the two
-- first instructions of @deleteTrace
--
-- >>> exampleCustom
-- [(Right (),fromList [("anew",1),("bnew",2),("c",3),("d",4)])]

exampleCustom :: [(Either KeyValueError (), Map String Integer)]
exampleCustom =
  interpretAndRun
    $ modifyLtl
      ( LtlAnd
          (LtlAtom $ renameKeys (++ "new"))
          (LtlNext $ LtlAtom $ renameKeys (++ "new"))
      )
    $ do
      storeValue "a" 1
      storeValue "b" 2
      storeValue "c" 3
      storeValue "d" 4
