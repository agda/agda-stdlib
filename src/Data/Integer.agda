------------------------------------------------------------------------
-- The Agda standard library
--
-- Integers
------------------------------------------------------------------------

-- See README.Data.Integer for examples of how to use and reason about
-- integers.

{-# OPTIONS --without-K --safe #-}

module Data.Integer where

import Data.Nat.Show as ℕ
open import Data.Sign as Sign using (Sign)
open import Data.String.Base using (String; _++_)

------------------------------------------------------------------------
-- Re-export basic definition, operations and queries

open import Data.Integer.Base public
open import Data.Integer.Properties public
  using (_≟_; _≤?_; _<?_)

------------------------------------------------------------------------
-- Conversions

show : ℤ → String
show i = showSign (sign i) ++ ℕ.show ∣ i ∣
  where
  showSign : Sign → String
  showSign Sign.- = "-"
  showSign Sign.+ = ""

------------------------------------------------------------------------
-- Deprecated

-- Version 0.17

open import Data.Integer.Properties public
  using (◃-cong; drop‿+≤+; drop‿-≤-)
  renaming (◃-inverse to ◃-left-inverse)
