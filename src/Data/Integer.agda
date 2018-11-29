------------------------------------------------------------------------
-- The Agda standard library
--
-- Integers
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Integer where

import Data.Nat.Show as ℕ
open import Data.Sign as Sign using (Sign)
open import Data.String.Base using (String; _++_)

------------------------------------------------------------------------
-- Integers, basic types and operations

open import Data.Integer.Base public

------------------------------------------------------------------------
-- Re-export queries from the properties modules

open import Data.Integer.Properties public
  using (_≟_; _≤?_)

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
