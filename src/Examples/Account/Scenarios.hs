{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Examples.Account.Scenarios where

import Control.Monad
import Examples.Account.AbstractDomain
import Examples.Account.PaymentMod
import Logic.Ltl

-- * Some policies, some of them purposely bugged

-- Expectations: "policyAlwaysReceives" will only accept payments
-- that increase the balance of "me"
--
-- Reality: since it is possible to exchange negative amounts, being
-- the actual recipient of payments is not sufficient.
policyAlwaysReceives :: Policy
policyAlwaysReceives (_, _, recipient) _ me = recipient == me

-- Expectations: "policyNeverNegative" will never accept payments
-- that leave the balance negative.
--
-- Reality: balance should be checked to be positive after the payment
-- has been made, not before.
policyNeverNegative :: Policy
policyNeverNegative _ bal _ = bal > 0

policyOtherNeverNegative :: Policy
policyOtherNeverNegative (_, amount, _) bal _ = bal - amount >= 0

-- This policy ensures that the exchange of money cannot be negative
policyPositivePayments :: Policy
policyPositivePayments (_, amount, _) _ _ = amount > 0

-- * A few scenarios helpers and scenarios

registerPolicies :: (MonadAccounts m) => m ()
registerPolicies = do
  addPolicy "alwaysReceives" policyAlwaysReceives
  addPolicy "neverNegative" policyNeverNegative
  addPolicy "positiveAmount" policyPositivePayments
  addPolicy "realAlwaysPositive" policyOtherNeverNegative

addAndSubscribe :: (MonadAccounts m) => String -> Integer -> [String] -> m ()
addAndSubscribe user bal = (addUser user bal >>) . mapM_ (subscribeToPolicy user)

registerUsers :: (MonadAccounts m) => m ()
registerUsers = do
  addAndSubscribe "alice" 0 ["alwaysReceives"]
  addAndSubscribe "bob" 1000 []
  addAndSubscribe "judith" 500 ["neverNegative"]

firstPayments :: (MonadAccounts m) => m ()
firstPayments = do
  issuePayment ("bob", 400, "judith")
  issuePayment ("bob", 600, "alice")
  issuePayment ("judith", 600, "alice")

scenario1 :: (MonadAccounts m) => String -> m Integer
scenario1 user = do
  registerPolicies
  registerUsers
  firstPayments
  getUserBalance user

-- >>> [(Right -1200]
negateScenario1 = interpretAndRun (modifyLtl (everywhere negatePaymentsMod) (scenario1 "alice"))

scenario2 :: (MonadAccounts m) => m ()
scenario2 = do
  registerPolicies
  registerUsers
  forM_ ["alice", "bob", "judith"] (`subscribeToPolicy` "positiveAmount")
  firstPayments

-- >>> [Left PolicyError,Left PolicyError,Left PolicyError]
negateScenario2 = interpretAndRun (modifyLtl (somewhere negatePaymentsMod) scenario2)

-- >>> [Right (-200)]
increaseJudithPaymentsScenario1 = interpretAndRun (modifyLtl (somewhere $ increaseJudithPaymentsMod 500) (scenario1 "judith"))

scenario3 :: (MonadAccounts m) => m Integer
scenario3 = do
  registerPolicies
  registerUsers
  subscribeToPolicy "judith" "realAlwaysPositive"
  firstPayments
  getUserBalance "judith"

-- >>> [Left PolicyError]
increaseJudithPaymentsScenario3 = interpretAndRun (modifyLtl (somewhere $ increaseJudithPaymentsMod 500) scenario3)
