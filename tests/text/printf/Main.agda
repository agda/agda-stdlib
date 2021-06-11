{-# OPTIONS --guardedness #-}

module Main where

open import Data.Integer.Base as ℤ using (+_)
open import Data.Integer.Literals
open import Data.Integer.GCD
open import Data.Integer.LCM
open import Data.Nat.Base
open import Data.String.Base
open import Data.Unit.Base
open import Function.Base using (_$_)
open import IO.Base
open import IO.Finite

open import Text.Printf

main : Main
main = run $ do
  let instance _ = negative
  putStrLn $ printf "%s: %u + %u ≡ %u" "example" 3 2 5
  putStrLn $ printf "%s: %u + %i ≡ %d" "example" 3 -3 (+ 3 ℤ.+ -3)
  putStrLn $ printf "gcd(%d,%i) ≡ %d" -9 (+ 15) (gcd -9 (+ 15))
  putStrLn $ printf "lcm(%d,%i) ≡ %d" -9 (+ 15) (lcm -9 (+ 15))
  putStrLn $ printf "A %s: %c" "char" 'c'
  putStrLn $ printf "A %s: %f" "float" 3.14
