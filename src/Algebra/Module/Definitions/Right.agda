------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of right-scaling
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

-- The properties are parameterised by the two carriers and
-- the result equality.

module Algebra.Module.Definitions.Right
  {a b ℓb} (A : Set a) {B : Set b} (_≈_ : Rel B ℓb)
  where

open import Data.Product
open import Data.Sum

------------------------------------------------------------------------
-- Binary operations

open import Algebra.Core

------------------------------------------------------------------------
-- Properties of operations

RightIdentity : A → Opᵣ A B → Set _
RightIdentity a _∙ᴮ_ = ∀ m → (m ∙ᴮ a) ≈ m

Associative : Op₂ A → Opᵣ A B → Set _
Associative _∙ᴬ_ _∙ᴮ_ = ∀ m x y → ((m ∙ᴮ x) ∙ᴮ y) ≈ (m ∙ᴮ (x ∙ᴬ y))

_DistributesOverˡ_⟶_ : Opᵣ A B → Op₂ A → Op₂ B → Set _
_*_ DistributesOverˡ _+ᴬ_ ⟶ _+ᴮ_ =
  ∀ m x y → (m * (x +ᴬ y)) ≈ ((m * x) +ᴮ (m * y))

_DistributesOverʳ_ : Opᵣ A B → Op₂ B → Set _
_*_ DistributesOverʳ _+_ =
  ∀ x m n → ((m + n) * x) ≈ ((m * x) + (n * x))

LeftZero : B → Opᵣ A B → Set _
LeftZero z _∙_ = ∀ x → (z ∙ x) ≈ z

RightZero : A → B → Opᵣ A B → Set _
RightZero zᴬ zᴮ _∙_ = ∀ x → (x ∙ zᴬ) ≈ zᴮ

Commutative : Opᵣ A B → Set _
Commutative _∙_ = ∀ m x y → ((m ∙ x) ∙ y) ≈ ((m ∙ y) ∙ x)

LeftCongruent : ∀ {ℓa} → Rel A ℓa → Opᵣ A B → Set _
LeftCongruent ≈ᴬ _∙_ = ∀ {m} → (m ∙_) Preserves ≈ᴬ ⟶ _≈_

RightCongruent : Opᵣ A B → Set _
RightCongruent _∙_ = ∀ {x} → (_∙ x) Preserves _≈_ ⟶ _≈_

Congruent : ∀ {ℓa} → Rel A ℓa → Opᵣ A B → Set _
Congruent ≈ᴬ ∙ = ∙ Preserves₂ _≈_ ⟶ ≈ᴬ ⟶ _≈_
