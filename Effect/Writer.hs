{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Effect.Writer where

import Control.Monad.Writer
import Effect
import Effect.TH
import Language.Haskell.TH

data WriterEffect w m a where
  Tell :: w -> WriterEffect w m ()
  Listen :: m a -> WriterEffect w m (a, w)
  Pass :: m (a, w -> w) -> WriterEffect w m a

makeReification
  (\ops -> [t|(Monoid $(varT (mkName "w")), EffectInject (WriterEffect $(varT (mkName "w"))) $(varT ops))|])
  [t|MonadWriter $(varT (mkName "w"))|]
  [t|WriterEffect $(varT (mkName "w"))|]

makeInterpretation
  (\m -> [t|(Monoid $(varT (mkName "w")), MonadWriter $(varT (mkName "w")) $(varT m))|])
  [t|WriterEffect $(varT (mkName "w"))|]
