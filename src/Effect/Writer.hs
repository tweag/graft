{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Effect.Writer where

import Control.Monad.Writer
import Effect
import Effect.TH
import Language.Haskell.TH

data WriterEffect w :: Effect where
  Tell :: w -> WriterEffect w m ()
  Listen :: m a -> WriterEffect w m (a, w)
  Pass :: m (a, w -> w) -> WriterEffect w m a

makeReification
  (\[w] _ -> [t|Monoid $(varT w)|])
  ''MonadWriter
  ''WriterEffect

makeInterpretation
  (\[w] _ -> [t|Monoid $(varT w)|])
  ''MonadWriter
  ''WriterEffect
