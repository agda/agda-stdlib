{-# OPTIONS --guardedness #-}

module runtests where

open import Data.List.Base as List using (_∷_; [])
open import Data.String.Base using (String; _++_)
open import IO.Base
open import Function.Base
open import Test.Golden

directoryTreeTests : TestPool
directoryTreeTests = mkTestPool "Directory Tree"
  $ "directory001"
  ∷ []

showTests : TestPool
showTests = mkTestPool "Show instances"
  $ "tree001"
  ∷ "num001"
  ∷ []

main : Main
main = run $ ignore $ runner
  $ testPaths "system" directoryTreeTests
  ∷ testPaths "show" showTests
  ∷ [] where

  testPaths : String -> TestPool -> TestPool
  testPaths dir pool =
    let testCases = List.map ((dir ++ "/") ++_) (pool .TestPool.testCases)
    in record pool { testCases = testCases }
