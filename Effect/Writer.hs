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

data WriterOperation w m a where
  Tell :: w -> WriterOperation w m ()
  Listen :: m a -> WriterOperation w m (a, w)
  Pass :: m (a, w -> w) -> WriterOperation w m a

makeReification
  (\ops -> [t|(Monoid $(varT (mkName "w")), OperationInject (WriterOperation $(varT (mkName "w"))) $(varT ops))|])
  [t|MonadWriter $(varT (mkName "w"))|]
  [t|WriterOperation $(varT (mkName "w"))|]

makeInterpretation
  (\m -> [t|(Monoid $(varT (mkName "w")), MonadWriter $(varT (mkName "w")) $(varT m))|])
  [t|WriterOperation $(varT (mkName "w"))|]
