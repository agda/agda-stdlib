------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers: sum and product of lists
--
-- Issue #2553: this is a compatibility stub module,
-- ahead of a more thorough breaking set of changes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.ListAction where

open import Data.List.Base using (List; []; _∷_; _++_; foldr)
open import Data.Nat.Base using (ℕ; _+_; _*_)


------------------------------------------------------------------------
-- Definitions

sum : List ℕ → ℕ
sum = foldr _+_ 0

product : List ℕ → ℕ
product = foldr _*_ 1
