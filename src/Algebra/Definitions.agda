------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of functions, such as associativity and commutativity
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra`, unless
-- you want to parameterise it via the equality relation.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Algebra.Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  where

open import Algebra.Core
open import Data.Product
open import Data.Sum.Base

------------------------------------------------------------------------
-- Properties of operations

Congruent₁ : Op₁ A → Set _
Congruent₁ f = f Preserves _≈_ ⟶ _≈_

Congruent₂ : Op₂ A → Set _
Congruent₂ ∙ = ∙ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_

LeftCongruent : Op₂ A → Set _
LeftCongruent _∙_ = ∀ {x} → (x ∙_) Preserves _≈_ ⟶ _≈_

RightCongruent : Op₂ A → Set _
RightCongruent _∙_ = ∀ {x} → (_∙ x) Preserves _≈_ ⟶ _≈_

Associative : Op₂ A → Set _
Associative _∙_ = ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))

Commutative : Op₂ A → Set _
Commutative _∙_ = ∀ x y → (x ∙ y) ≈ (y ∙ x)

LeftIdentity : A → Op₂ A → Set _
LeftIdentity e _∙_ = ∀ x → (e ∙ x) ≈ x

RightIdentity : A → Op₂ A → Set _
RightIdentity e _∙_ = ∀ x → (x ∙ e) ≈ x

Identity : A → Op₂ A → Set _
Identity e ∙ = (LeftIdentity e ∙) × (RightIdentity e ∙)

LeftZero : A → Op₂ A → Set _
LeftZero z _∙_ = ∀ x → (z ∙ x) ≈ z

RightZero : A → Op₂ A → Set _
RightZero z _∙_ = ∀ x → (x ∙ z) ≈ z

Zero : A → Op₂ A → Set _
Zero z ∙ = (LeftZero z ∙) × (RightZero z ∙)

LeftInverse : A → Op₁ A → Op₂ A → Set _
LeftInverse e _⁻¹ _∙_ = ∀ x → ((x ⁻¹) ∙ x) ≈ e

RightInverse : A → Op₁ A → Op₂ A → Set _
RightInverse e _⁻¹ _∙_ = ∀ x → (x ∙ (x ⁻¹)) ≈ e

Inverse : A → Op₁ A → Op₂ A → Set _
Inverse e ⁻¹ ∙ = (LeftInverse e ⁻¹) ∙ × (RightInverse e ⁻¹ ∙)

LeftConical : A → Op₂ A → Set _
LeftConical e _∙_ = ∀ x y → (x ∙ y) ≈ e → x ≈ e

RightConical : A → Op₂ A → Set _
RightConical e _∙_ = ∀ x y → (x ∙ y) ≈ e → y ≈ e

Conical : A → Op₂ A → Set _
Conical e ∙ = (LeftConical e ∙) × (RightConical e ∙)

_DistributesOverˡ_ : Op₂ A → Op₂ A → Set _
_*_ DistributesOverˡ _+_ =
  ∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))

_DistributesOverʳ_ : Op₂ A → Op₂ A → Set _
_*_ DistributesOverʳ _+_ =
  ∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x))

_DistributesOver_ : Op₂ A → Op₂ A → Set _
* DistributesOver + = (* DistributesOverˡ +) × (* DistributesOverʳ +)

_IdempotentOn_ : Op₂ A → A → Set _
_∙_ IdempotentOn x = (x ∙ x) ≈ x

Idempotent : Op₂ A → Set _
Idempotent ∙ = ∀ x → ∙ IdempotentOn x

IdempotentFun : Op₁ A → Set _
IdempotentFun f = ∀ x → f (f x) ≈ f x

Selective : Op₂ A → Set _
Selective _∙_ = ∀ x y → (x ∙ y) ≈ x ⊎ (x ∙ y) ≈ y

_Absorbs_ : Op₂ A → Op₂ A → Set _
_∙_ Absorbs _∘_ = ∀ x y → (x ∙ (x ∘ y)) ≈ x

Absorptive : Op₂ A → Op₂ A → Set _
Absorptive ∙ ∘ = (∙ Absorbs ∘) × (∘ Absorbs ∙)

Involutive : Op₁ A → Set _
Involutive f = ∀ x → f (f x) ≈ x

LeftCancellative : Op₂ A → Set _
LeftCancellative _•_ = ∀ x {y z} → (x • y) ≈ (x • z) → y ≈ z

RightCancellative : Op₂ A → Set _
RightCancellative _•_ = ∀ {x} y z → (y • x) ≈ (z • x) → y ≈ z

Cancellative : Op₂ A → Set _
Cancellative _•_ = (LeftCancellative _•_) × (RightCancellative _•_)

Interchangable : Op₂ A → Op₂ A → Set _
Interchangable _∘_ _∙_ = ∀ w x y z → ((w ∙ x) ∘ (y ∙ z)) ≈ ((w ∘ y) ∙ (x ∘ z))
