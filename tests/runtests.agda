{-# OPTIONS --guardedness #-}

module runtests where

open import Data.List.Base as List using (_∷_; [])
open import Data.String.Base using (String; _++_)
open import IO.Base
open import Function.Base
open import Test.Golden

dataTests : TestPool
dataTests = mkTestPool "Data structures"
  $ "appending"
  ∷ "colist"
  ∷ "list"
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

monadTests : TestPool
monadTests = mkTestPool "Monad transformers"
  $ "counting"
  ∷ "fibonacci"
  ∷ "pythagorean"
  ∷ "tcm"
  ∷ []

reflectionTests : TestPool
reflectionTests = mkTestPool "Reflection machinery"
  $ "assumption"
  ∷ []

main : Main
main = run $ ignore $ runner
  $ testPaths "data"          dataTests
  ∷ testPaths "monad"         monadTests
  ∷ testPaths "reflection"    reflectionTests
  ∷ testPaths "show"          showTests
  ∷ testPaths "system"        systemTests
  ∷ testPaths "text"          textTests
  ∷ [] where

  testPaths : String → TestPool → TestPool
  testPaths dir pool =
    let testCases = List.map ((dir ++ "/") ++_) (pool .TestPool.testCases)
    in record pool { testCases = testCases }
