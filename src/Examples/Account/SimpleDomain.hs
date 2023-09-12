{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImportQualifiedPost #-}

module Examples.Account.SimpleDomain where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Extra
import Control.Monad.State
import Data.Bifunctor (second)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Examples.Account.AbstractDomain

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

instance {-# OVERLAPPING #-} (MonadPlus m) => Alternative (AccountsT m) where
  empty = lift mzero
  ExceptT (StateT f) <|> ExceptT (StateT g) =
    ExceptT . StateT $ \s -> f s `mplus` g s

instance {-# OVERLAPPING #-} (MonadPlus m) => MonadPlus (AccountsT m)

-- * Some helper functions over AccountsT m

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

-- | A function to run the domain and return relevant information
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

  simulate comp = do
    current <- get
    x <- lift $ lift $ runAccountsT current comp
    return $ case fst x of
      (Left _) -> Nothing
      Right a -> Just a

  issuePayment payment@(sender, amount, recipient) = do
    (senderBal, senderPols) <- ensureExistingUser sender
    (recipientBal, recipientPols) <- ensureExistingUser recipient
    sPols <- foldM (\res el -> (\f -> f payment senderBal sender && res) <$> ensureExistingPolicy el) True senderPols
    unless sPols $ throwError PolicyError
    rPols <- foldM (\res el -> (\f -> f payment recipientBal recipient && res) <$> ensureExistingPolicy el) True recipientPols
    unless rPols $ throwError PolicyError
    modifyAccounts $ Map.insert recipient (recipientBal + amount, recipientPols)
    modifyAccounts $ Map.insert sender (senderBal - amount, senderPols)
