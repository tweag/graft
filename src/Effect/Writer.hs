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

data MonadWriterEffect w :: Effect where
  Tell :: w -> MonadWriterEffect w m ()
  Listen :: m a -> MonadWriterEffect w m (a, w)
  Pass :: m (a, w -> w) -> MonadWriterEffect w m a

makeEffect ''MonadWriter ''MonadWriterEffect
