{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Examples.Ltl.Accounts where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor (second)
import Data.Either (isRight)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Effect.Error
import Effect.Error.Passthrough ()
import Effect.TH
import Logic.Ltl
import Logic.SingleStep

-- * Depiction of the domain

-- | A payment contains a sender, an amount and a recipient
type Payment = (String, Integer, String)

-- | The type for validators
type Policy =
  -- | The payment currently validated
  Payment ->
  -- | The funds possessed by the current user
  Integer ->
  -- | The current user for which validation is called
  String ->
  -- | Returns whether the payment should go through
  Bool

-- | The register associates:
--
-- - policy names with policies
--
-- - users with a balance and a set of policy names
type Account = (Integer, Set String)

data Register = Register
  { policies :: Map String Policy,
    accounts :: Map String Account
  }

initialRegister :: Register
initialRegister = Register Map.empty Map.empty

-- | Our domain specification: users can be added, payments can be
-- attempted and balances can be requested.
class (Monad m) => MonadAccounts m where
  addUser :: String -> Integer -> m ()
  addPolicy :: String -> Policy -> m ()
  allPolicies :: m [String]
  subscribeToPolicy :: String -> String -> m ()
  unsubscribeToPolicy :: String -> String -> m ()
  anticipate :: m a -> m Bool
  issuePayment :: Payment -> m ()
  getUserBalance :: String -> m Integer

-- | Errors raised by the domain
data AccountsError
  = NoSuchAccount String
  | AlreadyExistingAccount String
  | NoSuchPolicy String
  | AlreadyExistingPolicy String
  | PolicyError
  deriving (Show)

-- | Our domain implementation
type AccountsT m = ExceptT AccountsError (StateT Register m)

-- * Some helper functions over AccountsT m

-- | Like @if@, but where the test can be monadic.
ifM :: (Monad m) => m Bool -> m a -> m a -> m a
ifM bM t f = do b <- bM; if b then t else f

-- | Like 'when', but where the test can be monadic.
whenM :: (Monad m) => m Bool -> m () -> m ()
whenM b t = ifM b t (pure ())

maybeM :: (Monad m) => m b -> (a -> m b) -> m (Maybe a) -> m b
maybeM n j x = maybe n j =<< x

-- | Ensures a user is registered and returns the associated account
ensureExistingUser :: (Monad m) => String -> AccountsT m Account
ensureExistingUser name =
  maybeM (throwError $ NoSuchAccount name) return $ gets $ Map.lookup name . accounts

-- | Ensures a user is not registered
ensureNonExistingUser :: (Monad m) => String -> AccountsT m ()
ensureNonExistingUser name =
  whenM (gets $ (name `Map.member`) . accounts) $ throwError $ AlreadyExistingAccount name

-- | Modifies the current map of accounts
modifyAccounts :: (Monad m) => (Map String Account -> Map String Account) -> AccountsT m ()
modifyAccounts f = modify $ \(Register pols accs) -> Register pols $ f accs

-- | Ensures a policy is registered and executes an action based on its value
ensureExistingPolicy :: (Monad m) => String -> AccountsT m Policy
ensureExistingPolicy name =
  maybeM (throwError $ NoSuchPolicy name) return $ gets $ Map.lookup name . policies

-- | Ensures a policy is not present and executes an action
ensureNonExistingPolicy :: (Monad m) => String -> AccountsT m ()
ensureNonExistingPolicy name =
  whenM (gets $ (name `Map.member`) . policies) $ throwError $ AlreadyExistingPolicy name

-- | Modifies the current map of policies
modifyPolicies :: (Monad m) => (Map String Policy -> Map String Policy) -> AccountsT m ()
modifyPolicies f = modify $ \(Register pols accs) -> flip Register accs $ f pols

-- | A function to run the domain into the list monad and return
-- relevant information
runAccountsT :: (Monad m) => Register -> AccountsT m a -> m (Either AccountsError a, Map String Account)
runAccountsT register comp = second accounts <$> runStateT (runExceptT comp) register

instance (Monad m) => MonadAccounts (AccountsT m) where
  addUser name balance = do
    ensureNonExistingUser name
    modifyAccounts $ Map.insert name (balance, Set.empty)

  addPolicy name val = do
    ensureNonExistingPolicy name
    modifyPolicies $ Map.insert name val

  subscribeToPolicy userName polName = do
    (bal, accPols) <- ensureExistingUser userName
    void $ ensureExistingPolicy polName
    modifyAccounts $ Map.insert userName (bal, Set.insert polName accPols)

  unsubscribeToPolicy userName polName = do
    (bal, accPols) <- ensureExistingUser userName
    modifyAccounts $ Map.insert userName (bal, Set.delete polName accPols)

  allPolicies = gets $ Map.keys . policies

  getUserBalance = (fst <$>) . ensureExistingUser

  anticipate comp = do
    current <- get
    isRight . fst <$> lift (lift $ runAccountsT current comp)

  issuePayment payment@(sender, amount, recipient) = do
    (senderBal, senderPols) <- ensureExistingUser sender
    (recipientBal, recipientPols) <- ensureExistingUser recipient
    sPols <- foldM (\res el -> (\f -> f payment senderBal sender && res) <$> ensureExistingPolicy el) True senderPols
    unless sPols $ throwError PolicyError
    rPols <- foldM (\res el -> (\f -> f payment recipientBal recipient && res) <$> ensureExistingPolicy el) True recipientPols
    unless rPols $ throwError PolicyError
    modifyAccounts $ Map.insert recipient (recipientBal + amount, recipientPols)
    modifyAccounts $ Map.insert sender (senderBal - amount, senderPols)

-- * Some (possibly bugged) validators

-- Expectations: "validatorAlwaysReceives" will only accept payments
-- that increase the balance of "me"
--
-- Reality: since it is possible to exchange negative amounts, being
-- the actual recipient is not sufficient.
validatorAlwaysReceives :: Policy
validatorAlwaysReceives (_, _, recipient) _ me = recipient == me

validatorAcceptsAll :: Policy
validatorAcceptsAll _ _ _ = True

-- Expectations: "validatorNeverNegative" will never accept payments
-- that leave the balance negative.
--
-- Reality: balance should be checked to be positive after the payment
-- has been made, not before.
validatorNeverNegative :: Policy
validatorNeverNegative _ bal _ = bal > 0

-- * A few scenarios that exhibit no wrong behavior

baseScenario :: (MonadAccounts m) => m ()
baseScenario = do
  addPolicy "alwaysReceives" validatorAlwaysReceives
  addPolicy "acceptsAll" validatorAcceptsAll
  addPolicy "neverNegative" validatorNeverNegative
  addUser "alice" 0
  subscribeToPolicy "alice" "alwaysReceives"
  addUser "bob" 1000
  subscribeToPolicy "bob" "acceptsAll"
  addUser "judith" 500
  subscribeToPolicy "judith" "neverNegative"

firstPayments :: (MonadAccounts m) => m ()
firstPayments = do
  issuePayment ("bob", 400, "judith")
  issuePayment ("bob", 600, "alice")
  issuePayment ("judith", 600, "alice")

alwaysReceivesAttempt :: (MonadAccounts m) => m Bool
alwaysReceivesAttempt = do
  baseScenario
  res <- anticipate $ do
    firstPayments
  when res firstPayments
  return res

defineEffectType ''MonadAccounts
makeEffect ''MonadAccounts ''MonadAccountsEffect

data AccountsMod where
  AccountsMod :: (Payment -> Maybe Payment) -> AccountsMod

instance Semigroup AccountsMod where
  (AccountsMod f1) <> (AccountsMod f2) =
    AccountsMod
      (\x -> (f1 <=< f2) x <|> f1 x <|> f2 x)

instance
  (MonadError AccountsError m, MonadAccounts m) =>
  InterpretMod AccountsMod m MonadAccountsEffect
  where
  interpretMod (IssuePayment payment) = Visible $ \(AccountsMod modif) ->
    case modif payment of
      Nothing -> return Nothing
      (Just newPayment) -> Just <$> issuePayment newPayment
  interpretMod _ = Invisible

conditionalPaymentMod :: (String -> Bool) -> (String -> Bool) -> (Integer -> Maybe Integer) -> AccountsMod
conditionalPaymentMod condSender condRecipient change =
  AccountsMod $
    \(sender, amount, recipient) -> case (change amount, condSender sender && condRecipient recipient) of
      (Nothing, _) -> Nothing
      (_, False) -> Nothing
      (Just newAmount, True) -> Just (sender, newAmount, recipient)

increaseJudithPaymentsMod :: AccountsMod
increaseJudithPaymentsMod = conditionalPaymentMod (== "judith") (const True) (Just . (+ 500))

instance {-# OVERLAPPING #-} (MonadPlus m) => Alternative (AccountsT m) where
  empty = lift mzero
  ExceptT (StateT f) <|> ExceptT (StateT g) =
    ExceptT . StateT $ \s -> f s `mplus` g s

instance {-# OVERLAPPING #-} (MonadPlus m) => MonadPlus (AccountsT m)

interpretAndRun ::
  LtlAST AccountsMod '[MonadAccountsEffect, MonadErrorEffect AccountsError] a ->
  [(Either AccountsError a, Map String (Integer, Set String))]
interpretAndRun =
  runAccountsT initialRegister
    . interpretLtlAST
      @'[ InterpretModTag,
          InterpretEffectStatefulTag
        ]
