{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}

module Examples.Ltl.Accounts where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Data.Map qualified as Map

type Payment = (String, Integer, String)

type Validator = Payment -> Integer -> String -> Bool

type Register = Map.Map String (Integer, Validator)

class (Monad m) => MonadAccounts m where
  addUser :: String -> Validator -> Integer -> m ()
  issuePayment :: Payment -> m ()
  getBalance :: String -> m Integer

data AccountsError
  = NoSuchAccount String
  | AlreadyExistingAccount String
  | PaymentRefused
  deriving (Show)

type Accounts = ExceptT AccountsError (StateT Register Identity)

runAccounts :: Accounts a -> (Either AccountsError a, Register)
runAccounts = runIdentity . flip runStateT Map.empty . runExceptT

instance MonadAccounts Accounts where
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

-- This validator has a bug: since it is possible to exchange negative
-- amounts, being the actual recipient is not sufficient.
validatorAlwaysReceives :: Validator
validatorAlwaysReceives (_, _, recipient) _ me = recipient == me

validatorAcceptsAll :: Validator
validatorAcceptsAll _ _ _ = True

-- This validator has a bug: the balance should be checked to be
-- positive after the payment has been made, not before.
validatorNeverNegative :: Validator
validatorNeverNegative _ bal _ = bal > 0

scenario :: (MonadAccounts m) => m Integer
scenario = do
  addUser "alice" validatorAlwaysReceives 0
  addUser "bob" validatorAcceptsAll 1000
  addUser "judith" validatorNeverNegative 500
  issuePayment ("bob", 400, "judith")
  issuePayment ("bob", 600, "alice")
  issuePayment ("judith", 1000, "alice")
  getBalance "judith"
