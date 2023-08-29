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

module LtlSpec where

import Control.Monad.Writer
import qualified Data.Set as Set
import Effect
import Effect.TH
import Logic.Ltl
import Logic.SingleStep
import qualified Test.Tasty as Tasty
import Test.Tasty.HUnit ((@?=))
import qualified Test.Tasty.HUnit as Tasty

data TestEffect :: Effect where
  EmitInteger :: Integer -> TestEffect m ()
  GetInteger :: TestEffect m Integer

class (Monad m) => MonadTest m where
  emitInteger :: Integer -> m ()
  getInteger :: m Integer

makeEffect ''MonadTest ''TestEffect

type TestT m = WriterT [Integer] m

instance (Monad m) => MonadTest (TestT m) where
  getInteger = return 42
  emitInteger = tell . (: [])

type TestModification = Integer -> Integer

instance {-# OVERLAPPING #-} Semigroup TestModification where
  a <> b = a . b

instance (MonadTest m) => InterpretMod TestModification m TestEffect where
  interpretMod GetInteger _ = PassModification
  interpretMod (EmitInteger i) (Just f) = AttemptModification $ emitInteger (f i) >> return (Just ())
  interpretMod (EmitInteger i) Nothing = SkipModification

go :: LtlAST TestModification '[TestEffect] a -> [[Integer]]
go = execWriterT . interpretLtlAST @'[InterpretModTag]

nonemptyTraces :: [LtlAST TestModification '[TestEffect] ()]
nonemptyTraces =
  [ getInteger >>= emitInteger,
    emitInteger 1 >> emitInteger 2,
    emitInteger 1 >> getInteger >>= emitInteger >> emitInteger 2
  ]

emptyTraces :: [LtlAST TestModification '[TestEffect] ()]
emptyTraces = [return ()]

testTraces :: [LtlAST TestModification '[TestEffect] ()]
testTraces = nonemptyTraces ++ emptyTraces

assertAll :: (a -> Tasty.Assertion) -> [a] -> Tasty.Assertion
assertAll = mapM_

assertEqualSets :: (Show a, Ord a) => [a] -> [a] -> Tasty.Assertion
assertEqualSets l r =
  Tasty.assertBool
    ( "unequal sets:\n"
        ++ "expected: "
        ++ show r
        ++ "\n"
        ++ " but got: "
        ++ show l
    )
    (Set.fromList l == Set.fromList r)

tests :: Tasty.TestTree
tests =
  Tasty.testGroup
    "Ltl"
    [ Tasty.testGroup
        "simple laws"
        [ Tasty.testCase "LtlFalsity fails on every computation" $
            assertAll (\tr -> go (modifyLtl LtlFalsity tr) @?= []) testTraces,
          Tasty.testCase "LtlTruth leaves every computation unchanged" $
            assertAll (\tr -> go (modifyLtl LtlTruth tr) @?= go tr) testTraces,
          Tasty.testCase "x `LtlUntil` y == y `LtlOr` (x `LtlAnd` LtlNext (x `LtlUntil` y))" $
            let x = LtlAtom (1 +)
                y = LtlAtom (2 +)
                a = x `LtlUntil` y
                b = y `LtlOr` (x `LtlAnd` LtlNext (x `LtlUntil` y))
             in assertAll
                  (\tr -> assertEqualSets (go $ modifyLtl a tr) (go $ modifyLtl b tr))
                  testTraces,
          Tasty.testCase "x `LtlRelease` y == y `LtlAnd` (x `LtlOr` LtlNext (x `LtlRelease` y)) for nonempty traces" $
            let x = LtlAtom (1 +)
                y = LtlAtom (2 +)
                a = x `LtlRelease` y
                b = y `LtlAnd` (x `LtlOr` LtlNext (x `LtlRelease` y))
             in assertAll
                  (\tr -> assertEqualSets (go $ modifyLtl a tr) (go $ modifyLtl b tr))
                  nonemptyTraces
        ],
      Tasty.testGroup
        "unit tests"
        [ Tasty.testCase "LtlNext changes the second step" $
            let n = 3

                incSeconds :: [[Integer]] -> [[Integer]]
                incSeconds = filter (/= []) . map incSecond
                  where
                    incSecond (a : b : cs) = a : b + n : cs
                    incSecond _ = []
             in assertAll
                  ( \tr ->
                      assertEqualSets
                        (go $ modifyLtl (LtlNext $ LtlAtom (n +)) tr)
                        (incSeconds $ go tr)
                  )
                  testTraces,
          Tasty.testCase
            "everywhere changes everything"
            $ let n = 3

                  incAll :: [[Integer]] -> [[Integer]]
                  incAll = map (map (+ n))
               in assertAll
                    (\tr -> assertEqualSets (go . modifyLtl (everywhere (n +)) $ tr) (incAll $ go tr))
                    testTraces,
          Tasty.testCase "somewhere case-splits" $
            let n = 3

                caseSplit :: [[Integer]] -> [[Integer]]
                caseSplit = concatMap alternatives
                  where
                    alternatives [] = []
                    alternatives (x : xs) = (x + n : xs) : map (x :) (alternatives xs)
             in assertAll
                  (\tr -> assertEqualSets (go . modifyLtl (somewhere (n +)) $ tr) (caseSplit $ go tr))
                  testTraces,
          Tasty.testCase "somewhere is exponential in branch number" $
            -- If we have @tr = a >> b@, we expect
            --
            -- > modifyLtl (somewhere f) $ modifyLtl (somewhere g) tr
            --
            -- to describe the following four traces:
            --
            -- > 1. f (g a) >> b
            -- > 2. f a >> g b
            -- > 3. g a >> f b
            -- > 4. a >> f (g b)
            --
            let tr = emitInteger 42 >> emitInteger 3
             in assertEqualSets
                  ( go $
                      modifyLtl (somewhere (1 +)) $
                        modifyLtl
                          (somewhere (2 +))
                          tr
                  )
                  [[42 + 1 + 2, 3], [42, 3 + 1 + 2], [42 + 1, 3 + 2], [42 + 2, 3 + 1]],
          Tasty.testCase "modality order is respected" $
            assertEqualSets
              ( go $
                  modifyLtl (everywhere (1 +)) $
                    modifyLtl (everywhere (const 2)) $
                      emitInteger 1
              )
              [[3]],
          Tasty.testCase "nested everywhere combines modifications" $
            assertEqualSets
              ( go $
                  modifyLtl (everywhere (1 +)) $ do
                    emitInteger 42
                    modifyLtl (everywhere (2 +)) $ do
                      emitInteger 43
                      modifyLtl (everywhere (3 *)) (emitInteger 44)
                    emitInteger 45
              )
              [[42 + 1, 43 + 1 + 2, 44 * 3 + 1 + 2, 45 + 1]]
        ]
    ]
