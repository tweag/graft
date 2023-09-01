{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Examples.Ltl.Accounts where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor (second)
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
data Register = Register
  { policies :: Map String Policy,
    accounts :: Map String (Integer, Set String)
  }

initialRegister :: Register
initialRegister = Register Map.empty Map.empty

-- | Our domain specification: users can be added, payments can be
-- attempted and balances can be requested.
class (Monad m) => MonadAccounts m where
  addUser :: String -> Integer -> m ()
  addPolicy :: String -> Policy -> m ()
  subscribeToPolicy :: String -> String -> m ()
  issuePayment :: Payment -> m ()
  getBalance :: String -> m Integer

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

-- | A function to run the domain into the list monad and return
-- relevant information
runAccountsT :: AccountsT [] a -> [(Either AccountsError a, Map String (Integer, Set String))]
runAccountsT =
  map (second accounts)
    . flip runStateT initialRegister
    . runExceptT

instance (Monad m) => MonadAccounts (AccountsT m) where
  addUser name balance = do
    accs <- gets accounts
    case Map.lookup name accs of
      Just _ -> throwError $ AlreadyExistingAccount name
      Nothing -> modify $ \x -> x {accounts = Map.insert name (balance, Set.empty) accs}
  addPolicy name val = do
    pols <- gets policies
    case Map.lookup name pols of
      Just _ -> throwError $ AlreadyExistingPolicy name
      Nothing -> modify $ \x -> x {policies = Map.insert name val pols}
  subscribeToPolicy userName polName = do
    Register pols accs <- get
    case Map.lookup userName accs of
      Nothing -> throwError $ NoSuchAccount userName
      Just (bal, accPols) ->
        if Map.member polName pols
          then modify $ \x -> x {accounts = Map.insert userName (bal, Set.insert polName accPols) accs}
          else throwError $ NoSuchPolicy polName
  getBalance name = do
    accs <- gets accounts
    case Map.lookup name accs of
      Nothing -> throwError $ NoSuchAccount name
      Just (bal, _) -> return bal
  issuePayment payment@(sender, amount, recipient) = do
    Register pols accs <- get
    case Map.lookup sender accs of
      Nothing -> throwError $ NoSuchAccount sender
      Just (senderBal, senderPols) -> case Map.lookup recipient accs of
        Nothing -> throwError $ NoSuchAccount recipient
        Just (recipientBal, recipientPols) -> do
          sPols <- foldM (\current el -> (\f -> f payment senderBal sender && current) <$> getPolicy pols el) True senderPols
          unless sPols $ throwError PolicyError
          rPols <- foldM (\current el -> (\f -> f payment recipientBal recipient && current) <$> getPolicy pols el) True recipientPols
          unless rPols $ throwError PolicyError
          let accs' = Map.insert sender (senderBal - amount, senderPols) accs
          modify $ \x -> x {accounts = Map.insert recipient (recipientBal + amount, recipientPols) accs'}
    where
      getPolicy pols x = case Map.lookup x pols of
        Nothing -> throwError $ NoSuchPolicy x
        Just cPol -> return cPol

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

scenario :: (MonadAccounts m) => m Integer
scenario = do
  addPolicy "alwaysReceives" validatorAlwaysReceives
  addPolicy "acceptsAll" validatorAcceptsAll
  addPolicy "neverNegative" validatorNeverNegative
  addUser "alice" 0
  subscribeToPolicy "alice" "alwaysReceives"
  addUser "bob" 1000
  subscribeToPolicy "bob" "acceptsAll"
  addUser "judith" 500
  subscribeToPolicy "judith" "neverNegative"
  issuePayment ("bob", 400, "judith")
  issuePayment ("bob", 600, "alice")
  issuePayment ("judith", 600, "alice")
  getBalance "judith"

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
  runAccountsT
    . interpretLtlAST
      @'[ InterpretModTag,
          InterpretEffectStatefulTag
        ]
