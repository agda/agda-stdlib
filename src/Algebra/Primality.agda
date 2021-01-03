------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of irreducibility, primality, coprimality.
------------------------------------------------------------------------

-- You're unlikely to want to use this module directly. Instead you
-- probably want to be importing the appropriate module from e.g.
-- `Algebra.Properties.Semiring.Primality`.

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core using (Op₂)
open import Data.Sum using (_⊎_)
open import Function using (flip)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; Symmetric)
open import Relation.Nullary using (¬_)

module Algebra.Primality
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_*_ : Op₂ A) (0# 1# : A)
  where

open import Algebra.Divisibility _≈_ _*_

------------------------------------------------------------------------------
-- Definitions

Coprime : Rel A (a ⊔ ℓ)
Coprime x y = ∀ {z} → z ∣ x → z ∣ y → z ∣ 1#

record Irreducible (p : A) : Set (a ⊔ ℓ) where
  constructor mkIrred
  field
    p∤1       : p ∤ 1#
    split-∣1 : ∀ {x y} → p ≈ (x * y) → x ∣ 1# ⊎ y ∣ 1#

record Prime (p : A) : Set (a ⊔ ℓ) where
  constructor mkPrime
  field
    p≉0     : ¬ (p ≈ 0#)
    split-∣ : ∀ {x y} → p ∣ x * y → p ∣ x ⊎ p ∣ y
