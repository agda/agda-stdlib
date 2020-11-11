------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of GCD.
------------------------------------------------------------------------

-- You're unlikely to want to use this module directly. Instead you
-- probably want to be importing the appropriate module from
-- `Algebra.Properties.CancellativeCommutativeSemiring`.

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core using (Op₂)
import Algebra.Divisibility
open import Level using (_⊔_)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_)

module Algebra.GCD {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_*_ : Op₂ A) where

open import Algebra.Divisibility _≈_ _*_

------------------------------------------------------------------------------
-- Definitions

private
  infix 4 _≉_

  _≉_ : Rel A _
  x ≉ y = ¬ (x ≈ y)

record GCD (arg1 arg2 : A) :  Set (a ⊔ ℓ) where      -- a result of gcd
  constructor gcdᶜ
  -- Greatest common divisor.

  field
    proper   : A                 -- the proper gcd value
    divides₁ : proper ∣ arg1
    divides₂ : proper ∣ arg2
    greatest : ∀ {x} → (x ∣ arg1) → (x ∣ arg2) → (x ∣ proper)
