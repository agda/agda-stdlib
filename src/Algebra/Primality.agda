------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of irreducibility, primality, coprimality.
------------------------------------------------------------------------

-- You're unlikely to want to use this module directly. Instead you
-- probably want to be importing the appropriate module from
-- `Algebra.Properties.CancellativeCommutativeSemiring`.

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core using (Op₂)
import Algebra.Divisibility
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Function using (flip)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; Symmetric)
open import Relation.Nullary using (¬_)
open import Relation.Unary using (Pred)

module Algebra.Primality
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_*_ : Op₂ A) (0# 1# : A)
  where

open import Algebra.Divisibility _≈_ _*_

------------------------------------------------------------------------------
-- Definitions

private
  infix 4 _≉_

  _≉_ : Rel A _
  x ≉ y = ¬ (x ≈ y)

IsIrreducible : Pred A (a ⊔ ℓ)
IsIrreducible p = p ∤ 1#  ×  (∀ {x y} → (p ≈ (x * y)) → x ∣ 1# ⊎ y ∣ 1#)

IsPrime : Pred A (a ⊔ ℓ)
IsPrime p = p ≉ 0#  ×  p ∤ 1#  ×  ∀ {x y} → p ∣ (x * y) → p ∣ x ⊎ p ∣ y

-- In a GCDDomain,  IsIrreducible is equivalent to IsPrime.
-- But in the general situation IsPrime is stronger.

Coprime : Rel A (a ⊔ ℓ)
Coprime a b = ∀ {x} → x ∣ a → x ∣ b → x ∣ 1#

------------------------------------------------------------------------------
-- Properties

Coprime-sym : Symmetric Coprime
Coprime-sym coprime = flip coprime
