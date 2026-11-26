------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers: sum and product of lists
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Data.Rational.ListAction where

open import Data.List.Base using (List; foldr)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)

------------------------------------------------------------------------
-- Definitions

sum : List ℚ → ℚ
sum = foldr _+_ 0ℚ

product : List ℚ → ℚ
product = foldr _*_ 1ℚ
