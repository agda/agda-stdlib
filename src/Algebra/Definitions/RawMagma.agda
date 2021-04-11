------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic auxiliary definitions for magma-like structures
------------------------------------------------------------------------

-- You're unlikely to want to use this module directly. Instead you
-- probably want to be importing the appropriate module from
-- `Algebra.Properties.(Magma/Semigroup/...).Divisibility`

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (RawMagma)
open import Data.Product using (_×_; ∃)
open import Level using (_⊔_)
open import Relation.Binary.Core
open import Relation.Nullary using (¬_)

module Algebra.Definitions.RawMagma
  {a ℓ} (M : RawMagma a ℓ)
  where

open RawMagma M renaming (Carrier to A)

------------------------------------------------------------------------
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

-- General divisibility

-- The relations _∣ˡ_ and _∣ʳ_ are only equivalent when _∙_ is
-- commutative. When that is not the case we take `_∣ʳ_` to be the
-- primary one.

_∣_ : Rel A (a ⊔ ℓ)
_∣_ = _∣ʳ_

_∤_ : Rel A (a ⊔ ℓ)
x ∤ y = ¬ x ∣ y

------------------------------------------------------------------------
-- Mutual divisibility.

-- In a  monoid, this is an equivalence relation extending _≈_.
-- When in a cancellative monoid,  elements related by _∣∣_ are called
-- associated, and `x ∣∣ y` means that `x` and `y` differ by some
-- invertible factor.

-- Example: for ℕ  this is equivalent to x ≡ y,
--          for ℤ  this is equivalent to (x ≡ y or x ≡ - y).

_∣∣_ : Rel A (a ⊔ ℓ)
x ∣∣ y = x ∣ y × y ∣ x

_∤∤_ : Rel A (a ⊔ ℓ)
x ∤∤ y = ¬ x ∣∣ y
