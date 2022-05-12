{-# OPTIONS --guardedness #-}

module runtests where

open import Data.List.Base as List using (_∷_; [])
open import Data.String.Base using (String; _++_)
open import IO.Base
open import Function.Base
open import Test.Golden

dataTests : TestPool
dataTests = mkTestPool "Data structures"
  $ "colist"
  ∷ "list"
  ∷ "appending"
  ∷ "rational"
  ∷ "rational-unnormalised"
  ∷ "trie"
  ∷ []

systemTests : TestPool
systemTests = mkTestPool "System modules"
  $ "ansi"
  ∷ "directory"
  ∷ "environment"
  ∷ []

showTests : TestPool
showTests = mkTestPool "Show instances"
  $ "num"
  ∷ "reflection"
  ∷ "tree"
  ∷ []

textTests : TestPool
textTests = mkTestPool "Text libraries"
  $ "pretty"
  ∷ "printf"
  ∷ "regex"
  ∷ "tabular"
  ∷ []

main : Main
main = run $ ignore $ runner
  $ testPaths "system" systemTests
  ∷ testPaths "show"   showTests
  ∷ testPaths "text"   textTests
  ∷ testPaths "data"   dataTests
  ∷ [] where

  testPaths : String → TestPool → TestPool
  testPaths dir pool =
    let testCases = List.map ((dir ++ "/") ++_) (pool .TestPool.testCases)
    in record pool { testCases = testCases }
