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
import Data.Map (Map)
import Data.Map qualified as Map
import Effect.Error
import Effect.Error.Passthrough ()
import Effect.TH
import Logic.Ltl
import Logic.SingleStep

type Payment = (String, Integer, String)

type Validator = Payment -> Integer -> String -> Bool

type Register = Map String (Integer, Validator)

class (Monad m) => MonadAccounts m where
  addUser :: String -> Validator -> Integer -> m ()
  issuePayment :: Payment -> m ()
  getBalance :: String -> m Integer

data AccountsError
  = NoSuchAccount String
  | AlreadyExistingAccount String
  | PaymentRefused
  deriving (Show)

type AccountsT m = ExceptT AccountsError (StateT Register m)

instance {-# OVERLAPPING #-} (MonadPlus m) => Alternative (AccountsT m) where
  empty = lift mzero
  ExceptT (StateT f) <|> ExceptT (StateT g) =
    ExceptT . StateT $ \s -> f s `mplus` g s

instance {-# OVERLAPPING #-} (MonadPlus m) => MonadPlus (AccountsT m)

runAccountsT :: AccountsT m a -> m (Either AccountsError a, Register)
runAccountsT = flip runStateT Map.empty . runExceptT

instance (Monad m) => MonadAccounts (AccountsT m) where
  addUser name val balance = do
    user <- gets (Map.lookup name)
    case user of
      Just _ -> throwError $ AlreadyExistingAccount name
      Nothing -> modify $ Map.insert name (balance, val)
  issuePayment t@(sender, amount, recipient) = do
    senderInfos <- gets (Map.lookup sender)
    recipientInfos <- gets (Map.lookup recipient)
    case (senderInfos, recipientInfos) of
      (Nothing, _) -> throwError $ NoSuchAccount sender
      (_, Nothing) -> throwError $ NoSuchAccount recipient
      (Just (sBal, sVal), Just (rBal, rVal)) ->
        if sVal t sBal sender && rVal t rBal recipient
          then do
            modify $ Map.insert sender (sBal - amount, sVal)
            modify $ Map.insert recipient (rBal + amount, rVal)
          else throwError PaymentRefused
  getBalance name = do
    user <- gets (Map.lookup name)
    case user of
      Just (bal, _) -> return bal
      Nothing -> throwError $ NoSuchAccount name

-- Expectations: "validatorAlwaysReceives" will only accept payments
-- that increase the balance of "me"
--
-- Reality: since it is possible to exchange negative amounts, being
-- the actual recipient is not sufficient.
validatorAlwaysReceives :: Validator
validatorAlwaysReceives (_, _, recipient) _ me = recipient == me

validatorAcceptsAll :: Validator
validatorAcceptsAll _ _ _ = True

-- Expectations: "validatorNeverNegative" will never accept payments
-- that leave the balance negative.
--
-- Reality: balance should be checked to be positive after the payment
-- has been made, not before.
validatorNeverNegative :: Validator
validatorNeverNegative _ bal _ = bal > 0

scenario :: (MonadAccounts m) => m Integer
scenario = do
  addUser "alice" validatorAlwaysReceives 0
  addUser "bob" validatorAcceptsAll 1000
  addUser "judith" validatorNeverNegative 500
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

paymentsInvolvingXMod :: String -> Bool -> (Integer -> Maybe Integer) -> AccountsMod
paymentsInvolvingXMod target isRecipient change =
  AccountsMod
    ( \(sender, amount, recipient) -> case change amount of
        Nothing -> Nothing
        Just x ->
          if target == (if isRecipient then recipient else sender)
            then Just (sender, x, recipient)
            else Nothing
    )

increaseJudithPaymentsMod :: AccountsMod
increaseJudithPaymentsMod =
  paymentsInvolvingXMod "judith" False (\x -> Just (x + 500))

interpretAndRun ::
  LtlAST AccountsMod '[MonadAccountsEffect, MonadErrorEffect AccountsError] a ->
  [(Either AccountsError a, Register)]
interpretAndRun =
  runAccountsT
    . interpretLtlAST
      @'[ InterpretModTag,
          InterpretEffectStatefulTag
        ]
