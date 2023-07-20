module Main where

import qualified LtlSpec as Ltl
import qualified Test.Tasty as Tasty

tests :: Tasty.TestTree
tests = Ltl.tests

main :: IO ()
main = Tasty.defaultMain tests
