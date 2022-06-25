------------------------------------------------------------------------
-- The Agda standard library
--
-- Postulated Real numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.PostulatedReal where

open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Publicly re-export contents of core module and queries

open import Data.PostulatedReal.Base public
open import Data.PostulatedReal.Properties.Core public
  using (_≟_; _≤?_; _<?_)

infixl 7 _⊓_
infixl 6 _⊔_

-- max
_⊔_ : ℝ → ℝ → ℝ
x ⊔ y with x ≤? y
... | yes _ = y
... | no  _ = x

-- min
_⊓_ : ℝ → ℝ → ℝ
x ⊓ y with x ≤? y
... | yes _ = x
... | no  _ = y

-- absolute value
∣_∣ : ℝ → ℝ
∣ x ∣  with 0ℝ ≤? x
... | yes _ = x
... | no  _ = - x

