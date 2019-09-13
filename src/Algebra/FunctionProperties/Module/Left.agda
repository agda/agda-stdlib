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

module Algebra.FunctionProperties.Module.Left
  {a b ℓa ℓb} {A : Set a} {B : Set b} (_≈ᴬ_ : Rel A ℓa) (_≈ᴮ_ : Rel B ℓb)
  where

open import Algebra.FunctionProperties.Core
open import Data.Product

------------------------------------------------------------------------
-- Binary operations

open import Algebra.FunctionProperties.Module.Core public

------------------------------------------------------------------------
-- Properties of operations

LeftIdentity : A → Opₗ A B → Set _
LeftIdentity a _∙ᴮ_ = ∀ m → (a ∙ᴮ m) ≈ᴮ m

Associative : Op₂ A → Opₗ A B → Set _
Associative _∙ᴬ_ _∙ᴮ_ = ∀ x y m → ((x ∙ᴬ y) ∙ᴮ m) ≈ᴮ (x ∙ᴮ (y ∙ᴮ m))

_DistributesOverˡ_ : Opₗ A B → Op₂ B → Set _
_*_ DistributesOverˡ _+_ =
  ∀ x m n → (x * (m + n)) ≈ᴮ ((x * m) + (x * n))

_DistributesOverʳ_⟶_ : Opₗ A B → Op₂ A → Op₂ B → Set _
_*_ DistributesOverʳ _+ᴬ_ ⟶ _+ᴮ_ =
  ∀ x m n → ((m +ᴬ n) * x) ≈ᴮ ((m * x) +ᴮ (n * x))

LeftZero : A → B → Opₗ A B → Set _
LeftZero zᴬ zᴮ _∙_ = ∀ x → (zᴬ ∙ x) ≈ᴮ zᴮ

RightZero : B → Opₗ A B → Set _
RightZero z _∙_ = ∀ x → (x ∙ z) ≈ᴮ z

Commutative : Opₗ A B → Set _
Commutative _∙_ = ∀ x y m → (x ∙ (y ∙ m)) ≈ᴮ (y ∙ (x ∙ m))

Congruent : Opₗ A B → Set _
Congruent _∙_ = ∀ {x x′ m m′} → x ≈ᴬ x′ → m ≈ᴮ m′ → (x ∙ m) ≈ᴮ (x′ ∙ m′)
