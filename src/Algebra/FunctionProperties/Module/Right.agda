------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of functions, such as associativity and commutativity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level
open import Relation.Binary
open import Data.Sum

-- The properties are parameterised by the following "equality"
-- relations

module Algebra.FunctionProperties.Module.Right
  {a b ℓa ℓb} {A : Set a} {B : Set b} (_≈ᴬ_ : Rel A ℓa) (_≈ᴮ_ : Rel B ℓb)
  where

open import Algebra.FunctionProperties.Core
open import Data.Product

------------------------------------------------------------------------
-- Binary operations

open import Algebra.FunctionProperties.Module.Core public

------------------------------------------------------------------------
-- Properties of operations

RightIdentity : A → Opᵣ A B → Set _
RightIdentity a _∙ᴮ_ = ∀ m → (m ∙ᴮ a) ≈ᴮ m

Associative : Op₂ A → Opᵣ A B → Set _
Associative _∙ᴬ_ _∙ᴮ_ = ∀ m x y → ((m ∙ᴮ x) ∙ᴮ y) ≈ᴮ (m ∙ᴮ (x ∙ᴬ y))

_DistributesOverˡ_⟶_ : Opᵣ A B → Op₂ A → Op₂ B → Set _
_*_ DistributesOverˡ _+ᴬ_ ⟶ _+ᴮ_ =
  ∀ m x y → (m * (x +ᴬ y)) ≈ᴮ ((m * x) +ᴮ (m * y))

_DistributesOverʳ_ : Opᵣ A B → Op₂ B → Set _
_*_ DistributesOverʳ _+_ =
  ∀ x m n → ((m + n) * x) ≈ᴮ ((m * x) + (n * x))

LeftZero : B → Opᵣ A B → Set _
LeftZero z _∙_ = ∀ x → (z ∙ x) ≈ᴮ z

RightZero : A → B → Opᵣ A B → Set _
RightZero zᴬ zᴮ _∙_ = ∀ x → (x ∙ zᴬ) ≈ᴮ zᴮ

Commutative : Opᵣ A B → Set _
Commutative _∙_ = ∀ m x y → ((m ∙ x) ∙ y) ≈ᴮ ((m ∙ y) ∙ x)

Congruent : Opᵣ A B → Set _
Congruent _∙_ = ∀ {m m′ x x′} → m ≈ᴮ m′ → x ≈ᴬ x′ → (m ∙ x) ≈ᴮ (m′ ∙ x′)
