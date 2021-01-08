-----------------------------------------------------------------------
-- The Agda standard library
--
-- Basic auxiliary definitions for magma-like structures
------------------------------------------------------------------------

-- You're unlikely to want to use this module directly. Instead you
-- probably want to be importing the appropriate module from
-- `Algebra.Properties.(Magma/Semigroup/...).Divisibility`

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; swap)
open import Algebra.Bundles using (RawMagma)
open import Data.Product using (∃; _×_; _,_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Nullary using (¬_)

module Algebra.Definitions.RawMagma
  {a ℓ} (M : RawMagma a ℓ)
  where

open RawMagma M renaming (Carrier to A)
open import Algebra.Definitions _≈_

-----------------------------------------------------------------------
-- Divisibility

infix 5 _∣ˡ_ _∤ˡ_ _∣ʳ_ _∤ʳ_ _∣_ _∤_

-- Divisibility from the left

_∣ˡ_ : Rel A (a ⊔ ℓ)
x ∣ˡ y = ∃ λ q → (x ∙ q) ≈ y

_∤ˡ_ : Rel A (a ⊔ ℓ)
x ∤ˡ y = ¬ x ∣ˡ y

-- Divisibility from the right

_∣ʳ_ : Rel A (a ⊔ ℓ)
x ∣ʳ y = ∃ λ q → (q ∙ x) ≈ y

_∤ʳ_ : Rel A (a ⊔ ℓ)
x ∤ʳ y = ¬ x ∣ʳ y

-- _∣ˡ_ and _∣ʳ_ are only equivalent in the commutative case. In this
-- case we take the right definition to be the primary one.

_∣_ : Rel A (a ⊔ ℓ)
_∣_ = _∣ʳ_

_∤_ : Rel A (a ⊔ ℓ)
x ∤ y = ¬ x ∣ y

------------------------------------------------------------------------
-- Mutual divisibility _∣∣_.
-- In a  monoid,  this is an equivalence relation extending _≈_.
-- When in a  cancellative monoid,  elements related by _∣∣_ are called
-- associated,  and there x ∣∣ y is equivalent to that x and y differ by
-- some invertible factor.
-- Example: for ℕ  this is equivalent to  x ≡ y,
--          for ℤ  this is equivalent to  (x ≡ y  or  x ≡ -y).

_∣∣_ : Rel A (a ⊔ ℓ)
x ∣∣ y = x ∣ y × y ∣ x

_∤∤_ : Rel A (a ⊔ ℓ)
x ∤∤ y =  ¬ x ∣∣ y

------------------------------------------------------------------------------
-- Greatest common divisor (GCD)

record IsGCD (x y gcd : A) : Set (a ⊔ ℓ) where
  constructor isGCDᶜ
  field
    divides₁ : gcd ∣ x
    divides₂ : gcd ∣ y
    greatest : ∀ {z} → z ∣ x → z ∣ y → z ∣ gcd

  quot₁ : A               -- a complementory quotient  x/gcd
  quot₁ = proj₁ divides₁

  quot₂ : A               -- y/gcd
  quot₂ = proj₁ divides₂

  quot₁∙gcd≈x : (quot₁ ∙ gcd) ≈ x
  quot₁∙gcd≈x = proj₂ divides₁

  quot₂∙gcd≈y : (quot₂ ∙ gcd) ≈ y
  quot₂∙gcd≈y = proj₂ divides₂
