{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Examples.Account.PaymentMod where

import Control.Applicative
import Control.Monad
import Data.Map qualified as Map
import Effect.Error
import Effect.Error.Passthrough ()
import Examples.Account.AbstractDomain
import Examples.Account.SimpleDomain
import Logic.Ltl
import Logic.SingleStep

data AccountsMod where
  AccountsMod :: (Payment -> Maybe Payment) -> AccountsMod

instance Semigroup AccountsMod where
  (AccountsMod f1) <> (AccountsMod f2) =
    AccountsMod
      (\x -> (f1 <=< f2) x <|> f1 x <|> f2 x)

instance
  (MonadAccounts m) =>
  InterpretMod AccountsMod m MonadAccountsEffect
  where
  interpretMod (IssuePayment payment) = Visible $ \(AccountsMod modif) ->
    maybe (return Nothing) ((Just <$>) . issuePayment) $ modif payment
  interpretMod _ = Invisible

instance
  (MonadAccounts m) =>
  InterpretLtlHigherOrder AccountsMod m MonadAccountsEffect
  where
  interpretLtlHigherOrder (Simulate comp) = Nested $ \evalAST ltls ->
    Just . (,ltls) . (fst <$>) <$> simulate (evalAST ltls comp)
  interpretLtlHigherOrder p = Direct $ interpretMod p

conditionalPaymentMod :: (String -> Bool) -> (String -> Bool) -> (Integer -> Maybe Integer) -> AccountsMod
conditionalPaymentMod condSender condRecipient change =
  AccountsMod $
    \(sender, amount, recipient) -> case (change amount, condSender sender && condRecipient recipient) of
      (Nothing, _) -> Nothing
      (_, False) -> Nothing
      (Just newAmount, True) -> Just (sender, newAmount, recipient)

increaseJudithPaymentsMod :: Integer -> AccountsMod
increaseJudithPaymentsMod n = conditionalPaymentMod (== "judith") (const True) (Just . (+ n))

negatePaymentsMod :: AccountsMod
negatePaymentsMod = conditionalPaymentMod (const True) (const True) (Just . negate)

interpretAndRun ::
  LtlAST AccountsMod '[MonadAccountsEffect, MonadErrorEffect AccountsError] a ->
  [Either AccountsError a]
interpretAndRun =
  (fst <$>)
    . runAccountsT (Register Map.empty Map.empty)
    . interpretLtlAST
      @'[ InterpretLtlHigherOrderTag,
          InterpretEffectStatefulTag
        ]
