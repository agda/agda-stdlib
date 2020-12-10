------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Integer.Show where

open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Nat.Base using (suc)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String.Base using (String; _++_)

------------------------------------------------------------------------
-- Show

-- Decimal notation: conversion back and forth with characters
-- Time complexity is O(log₁₀(n))

show : ℤ → String
show (+ n)    = showℕ n
show -[1+ n ] = "-" ++ showℕ (suc n)
