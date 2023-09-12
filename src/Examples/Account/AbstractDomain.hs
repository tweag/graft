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

module Examples.Account.AbstractDomain where

import Data.Map (Map)
import Data.Set (Set)
import Effect.TH

-- * Depiction of the domain

-- | A payment contains a sender, an amount and a recipient
type Payment = (String, Integer, String)

-- | The type for policies
type Policy =
  -- | The payment currently validated
  Payment ->
  -- | The funds possessed by the current user
  Integer ->
  -- | The current user for which validation is called
  String ->
  -- | Returns whether the payment should go through
  Bool

-- | An account contains the balance and set of policies
type Account = (Integer, Set String)

-- | The register associates:
--
-- - policy names with policies
--
-- - user names with accounts
data Register = Register
  { policies :: Map String Policy,
    accounts :: Map String Account
  }

-- | Our domain specification: users can be added, payments can be
-- attempted and balances can be requested.
class (Monad m) => MonadAccounts m where
  addUser :: String -> Integer -> m ()
  addPolicy :: String -> Policy -> m ()
  allPolicies :: m [String]
  subscribeToPolicy :: String -> String -> m ()
  unsubscribeToPolicy :: String -> String -> m ()
  simulate :: m a -> m (Maybe a)
  issuePayment :: Payment -> m ()
  getUserBalance :: String -> m Integer

-- | Effects for the abstract domain
defineEffectType ''MonadAccounts
makeEffect ''MonadAccounts ''MonadAccountsEffect
