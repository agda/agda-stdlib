{-# OPTIONS --guardedness --sized-types #-}

module Main where

open import Data.Integer.Base using (ℤ; +_)
import Data.Integer.Show as ℤ
open import Data.List.Base as List using (List; _∷_; [])
import Data.Nat.Base
open import Data.Rational.Unnormalised.Base
  using (ℚᵘ; -_; _/_; floor; ceiling; truncate; round; fracPart)
import Data.Rational.Unnormalised.Show as ℚᵘ
open import Data.String.Base as String using (String)

open import IO.Base
open import IO.Finite
open import Function.Base using (_$_)

testList : List ℚᵘ
testList = - (+ 35 / 10) ∷ - (+ 27 / 10) ∷ - (+ 15 / 10) ∷ - (+ 3 / 10)
         ∷ + 3 / 10 ∷ + 15 / 10 ∷ + 27 / 10 ∷ + 35 / 10 ∷ []

showInts : List ℤ → String
showInts is = String.concat
            $ "["
            ∷ String.intersperse ", " (List.map ℤ.show is)
            ∷ "]" ∷ []

showRats : List ℚᵘ → String
showRats ps = String.concat
            $ "["
            ∷ String.intersperse ", " (List.map ℚᵘ.show ps)
            ∷ "]" ∷ []

main : Main
main = run $ do
  putStrLn $ showInts (List.map floor testList)
  putStrLn $ showInts (List.map ceiling testList)
  putStrLn $ showInts (List.map truncate testList)
  putStrLn $ showInts (List.map round testList)
  putStrLn $ showRats (List.map fracPart testList)
