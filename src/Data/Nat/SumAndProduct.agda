------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers: sum and product of lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.SumAndProduct where

open import Data.Nat.Base using (ℕ; _+_; _*_)
open import Data.List.Base using (List; foldr)

sum : List ℕ → ℕ
sum = foldr _+_ 0

product : List ℕ → ℕ
product = foldr _*_ 1
