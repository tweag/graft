{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Logic.NextBind where

import Control.Monad
import Effect

data NextBind t x where
  DoNothing :: x -> NextBind t x
  Fail :: NextBind t ()
  Now :: t x -> NextBind t x
  Branch :: NextBind t x -> NextBind t x -> NextBind t x
  Next :: NextBind t y -> (y -> NextBind t x) -> NextBind t x

andLater :: t a -> (a -> t b) -> NextBind t b
andLater x y = Next (Now x) (Now . y)

somewhere :: t a -> NextBind t a
somewhere x = Branch (Now x) (Next (DoNothing ()) (const $ somewhere x))

everywhere :: t a -> NextBind t a
everywhere x = Next (Now x) (const $ everywhere x)

finished :: NextBind t x -> Bool
finished DoNothing {} = True
finished (Branch l r) = finished l || finished r
finished _ = False

immediate :: NextBind t x -> [x]
immediate (DoNothing x) = [x]
immediate (Branch l r) = immediate l ++ immediate r
immediate _ = []

data Interpretation t m ops a where
  Direct :: (forall x. t x -> m (Maybe (a, x))) -> Interpretation t m ops a
  Nested ::
    AST ops b ->
    (forall x. NextBind t x -> NextBind t x) ->
    (forall x. m (b, NextBind t x) -> m (a, NextBind t x)) ->
    Interpretation t m ops a

class InterpretNextBind t m op where
  interpretNextBind ::
    op (AST ops) a ->
    Interpretation t m ops a

instance (MonadPlus m, InterpretEffect m op, InterpretNextBind t m op) => InterpretEffectStateful (NextBind t) m op where
  interpretEffectStateful evalActs nextBind op =
    case interpretNextBind op of
      Nested acts changeMod wrap -> wrap $ evalActs (changeMod nextBind) acts
      Direct direct -> case nextBind of
        DoNothing x ->
          fmap (,DoNothing x) $
            interpretEffect (fmap fst . evalActs (DoNothing x)) op
        Fail -> mzero
        Now t -> do
          mAx <- direct t
          case mAx of
            Just (a, x) -> return (a, DoNothing x)
            Nothing -> mzero
        Next x y -> do
          (a, x') <- interpretEffectStateful evalActs x op
          if finished x'
            then msum $ map (return . (a,) . y) $ immediate x'
            else return (a, Next x' y)
        Branch l r ->
          interpretEffectStateful evalActs l op
            `mplus` interpretEffectStateful evalActs r op
