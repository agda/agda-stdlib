------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of functions, such as associativity and commutativity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

-- The properties are parameterised by the two carriers and
-- the result equality.

module Algebra.FunctionProperties.LeftAction
  {a b ℓb} (A : Set a) {B : Set b} (_≈_ : Rel B ℓb)
  where

open import Data.Sum
open import Data.Product

------------------------------------------------------------------------
-- Binary operations

open import Algebra.FunctionProperties.Core public

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

Congruent : ∀ {ℓa} → Rel A ℓa → Opₗ A B → Set _
Congruent _≈ᴬ_ _∙_ = ∀ {x x′ m m′} → x ≈ᴬ x′ → m ≈ m′ → (x ∙ m) ≈ (x′ ∙ m′)
