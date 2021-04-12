------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic auxiliary definitions for semiring-like structures
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (RawSemiring)
open import Data.Sum.Base using (_⊎_)
open import Data.Nat using (ℕ)
open import Level using (_⊔_)
open import Relation.Binary.Core using (Rel)

module Algebra.Definitions.RawSemiring {a ℓ} (M : RawSemiring a ℓ) where

open RawSemiring M renaming (Carrier to A)

------------------------------------------------------------------------
-- Definitions over _+_

open import Algebra.Definitions.RawMonoid +-rawMonoid public
  using
  ( _×_   -- : ℕ → A → A
  ; _×′_  -- : ℕ → A → A
  ; sum   -- : Vector A n → A
  )

------------------------------------------------------------------------
-- Definitions over _*_

open import Algebra.Definitions.RawMonoid *-rawMonoid as Mult public
  using
  ( _∣_
  ; _∤_
  )
  renaming
  ( sum to product
  )

-- Unlike `sum` to `product`, can't simply rename multiplication to
-- exponentation as the argument order is reversed.

-- Standard exponentiation

infixr 8 _^_
_^_ : A → ℕ → A
x ^ n  = n Mult.× x

-- Exponentiation optimsed for type-checking

infixr 8 _^′_
_^′_ : A → ℕ → A
x ^′ n  = n Mult.×′ x
{-# INLINE _^′_ #-}

------------------------------------------------------------------------
-- Primality

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
    p≉0     : p ≉ 0#
    split-∣ : ∀ {x y} → p ∣ x * y → p ∣ x ⊎ p ∣ y
