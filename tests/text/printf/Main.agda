{-# OPTIONS --guardedness #-}

module Main where

open import Data.Integer.Base as ℤ
open import Data.Nat.Base
open import Data.String.Base
open import Function.Base using (_$_)
open import IO.Base
open import IO.Finite

open import Text.Printf

main : Main
main = run $ do
  putStrLn $ printf "%s: %u + %u ≡ %u" "example" 3 2 5
  putStrLn $ printf "%s: %u + %i ≡ %d" "example" 3 -[1+ 2 ] (+ 3 ℤ.+ -[1+ 2 ])
  putStrLn $ printf "A %s: %c" "char" 'c'
  putStrLn $ printf "A %s: %f" "float" 3.14
