------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of left-scaling
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

-- The properties are parameterised by the two carriers and
-- the result equality.

module Algebra.Module.Definitions.Left
  {a b ℓb} (A : Set a) {B : Set b} (_≈_ : Rel B ℓb)
  where

open import Data.Sum
open import Data.Product

------------------------------------------------------------------------
-- Binary operations

open import Algebra.Core

------------------------------------------------------------------------
-- Properties of operations

LeftIdentity : A → Opₗ A B → Set _
LeftIdentity a _∙ᴮ_ = ∀ m → (a ∙ᴮ m) ≈ m

Associative : Op₂ A → Opₗ A B → Set _
Associative _∙ᴬ_ _∙ᴮ_ = ∀ x y m → ((x ∙ᴬ y) ∙ᴮ m) ≈ (x ∙ᴮ (y ∙ᴮ m))

_DistributesOverˡ_ : Opₗ A B → Op₂ B → Set _
_*_ DistributesOverˡ _+_ =
  ∀ x m n → (x * (m + n)) ≈ ((x * m) + (x * n))

_DistributesOverʳ_⟶_ : Opₗ A B → Op₂ A → Op₂ B → Set _
_*_ DistributesOverʳ _+ᴬ_ ⟶ _+ᴮ_ =
  ∀ x m n → ((m +ᴬ n) * x) ≈ ((m * x) +ᴮ (n * x))

LeftZero : A → B → Opₗ A B → Set _
LeftZero zᴬ zᴮ _∙_ = ∀ x → (zᴬ ∙ x) ≈ zᴮ

RightZero : B → Opₗ A B → Set _
RightZero z _∙_ = ∀ x → (x ∙ z) ≈ z

Commutative : Opₗ A B → Set _
Commutative _∙_ = ∀ x y m → (x ∙ (y ∙ m)) ≈ (y ∙ (x ∙ m))

LeftCongruent : Opₗ A B → Set _
LeftCongruent _∙_ = ∀ {x} → (x ∙_) Preserves _≈_ ⟶ _≈_

RightCongruent : ∀ {ℓa} → Rel A ℓa → Opₗ A B → Set _
RightCongruent ≈ᴬ _∙_ = ∀ {m} → (_∙ m) Preserves ≈ᴬ ⟶ _≈_

Congruent : ∀ {ℓa} → Rel A ℓa → Opₗ A B → Set _
Congruent ≈ᴬ ∙ = ∙ Preserves₂ ≈ᴬ ⟶ _≈_ ⟶ _≈_
