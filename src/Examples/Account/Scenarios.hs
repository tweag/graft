module Examples.Account.Scenarios where

import Control.Monad
import Data.Maybe
import Examples.Account.AbstractDomain

-- * Some validators, some of them purposely bugged

-- Expectations: "validatorAlwaysReceives" will only accept payments
-- that increase the balance of "me"
--
-- Reality: since it is possible to exchange negative amounts, being
-- the actual recipient of payments is not sufficient.
validatorAlwaysReceives :: Policy
validatorAlwaysReceives (_, _, recipient) _ me = recipient == me

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
  addPolicy "neverNegative" validatorNeverNegative
  addUser "alice" 0
  subscribeToPolicy "alice" "alwaysReceives"
  addUser "bob" 1000
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
  res <- simulate $ do
    firstPayments
  when (isJust res) firstPayments
  return $ isJust res
