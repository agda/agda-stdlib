------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of irreducibility, primality, coprimality, GCD.
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

module Algebra.GCD
  {β ℓ} {A : Set β} (_≈_ : Rel A ℓ) (0# 1# : A) (_*_ : Op₂ A)
  where

open import Algebra.Divisibility _≈_ _*_

------------------------------------------------------------------------------
-- Definitions

infix 4 _≉_

_≉_ : Rel A _
x ≉ y = ¬ (x ≈ y)

IsIrreducible : Pred A (β ⊔ ℓ)
IsIrreducible p = p ∤ 1#  ×  (∀ {x y} → (p ≈ (x * y)) → x ∣ 1# ⊎ y ∣ 1#)

IsPrime : Pred A (β ⊔ ℓ)
IsPrime p = p ≉ 0#  ×  p ∤ 1#  ×  ∀ {x y} → p ∣ (x * y) → p ∣ x ⊎ p ∣ y

-- In a GCDDomain,  IsIrreducible is equivalent to IsPrime.

Coprime : Rel A (β ⊔ ℓ)
Coprime a b = ∀ {c} → c ∣ a → c ∣ b → c ∣ 1#

record GCD (a b : A) :  Set (β ⊔ ℓ) where      -- a result of gcd
  constructor gcdᶜ
  -- Greatest common divisor.

  field
    proper   : A                 -- the proper gcd value
    divides₁ : proper ∣ a
    divides₂ : proper ∣ b
    greatest : ∀ {d} → (d ∣ a) → (d ∣ b) → (d ∣ proper)

------------------------------------------------------------------------------
-- Properties

Coprime-sym : Symmetric Coprime
Coprime-sym coprime = flip coprime
