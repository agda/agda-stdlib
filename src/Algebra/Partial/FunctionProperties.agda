------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of functions, such as associativity and commutativity.
-- These properties are based off of partial equivalence relations,
-- and require explicit proofs of reflexivity.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level
open import Relation.Binary
open import Relation.Binary.Partial
open import Data.Sum

-- The properties are parameterised by the following partial equivalence relation
module Algebra.Partial.FunctionProperties
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Data.Product

open import Algebra.FunctionProperties.Core public
-- We can re-use a few definitions
open import Algebra.FunctionProperties _≈_ using
  ( Congruent₁
  ; Congruent₂
  ) public
------------------------------------------------------------------------
-- Properties of operations

Associative : Op₂ A → Set _
Associative _∙_ = ∀ {x y z} → (x ≈ x) → (y ≈ y) → (z ≈ z) → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))

Commutative : Op₂ A → Set _
Commutative _∙_ = ∀ {x y} → (x ≈ x) → (y ≈ y) → (x ∙ y) ≈ (y ∙ x)

LeftIdentity : A → Op₂ A → Set _
LeftIdentity e _∙_ = ∀ {x} → (e ≈ e) → (x ≈ x) → (e ∙ x) ≈ x

RightIdentity : A → Op₂ A → Set _
RightIdentity e _∙_ = ∀ {x} → (e ≈ e) → (x ≈ x) → (x ∙ e) ≈ x

Identity : A → Op₂ A → Set _
Identity e ∙ = (LeftIdentity e ∙) × (RightIdentity e ∙)

LeftZero : A → Op₂ A → Set _
LeftZero z _∙_ = ∀ {x} → (z ≈ z) → (x ≈ x) → (z ∙ x) ≈ z

RightZero : A → Op₂ A → Set _
RightZero z _∙_ = ∀ {x} → (z ≈ z) → (x ≈ x) → (x ∙ z) ≈ z

Zero : A → Op₂ A → Set _
Zero z ∙ = (LeftZero z ∙) × (RightZero z ∙)

LeftInverse : A → Op₁ A → Op₂ A → Set _
LeftInverse e _⁻¹ _∙_ = ∀ {x} → (e ≈ e) → (x ≈ x) → ((x ⁻¹) ∙ x) ≈ e

RightInverse : A → Op₁ A → Op₂ A → Set _
RightInverse e _⁻¹ _∙_ = ∀ {x} → (e ≈ e) → (x ≈ x) → (x ∙ (x ⁻¹)) ≈ e

Inverse : A → Op₁ A → Op₂ A → Set _
Inverse e ⁻¹ ∙ = (LeftInverse e ⁻¹) ∙ × (RightInverse e ⁻¹ ∙)

LeftConical : A → Op₂ A → Set _
LeftConical e _∙_ = ∀ {x y} → (x ≈ x) → (y ≈ y) → (x ∙ y) ≈ e → x ≈ e

RightConical : A → Op₂ A → Set _
RightConical e _∙_ = ∀ {x y} → (x ≈ x) → (y ≈ y) → (x ∙ y) ≈ e → y ≈ e

Conical : A → Op₂ A → Set _
Conical e ∙ = (LeftConical e ∙) × (RightConical e ∙)

_DistributesOverˡ_ : Op₂ A → Op₂ A → Set _
_*_ DistributesOverˡ _+_ =
  ∀ {x y z} → (x ≈ x) → (y ≈ y) → (z ≈ z) → (x * (y + z)) ≈ ((x * y) + (x * z))

_DistributesOverʳ_ : Op₂ A → Op₂ A → Set _
_*_ DistributesOverʳ _+_ =
  ∀ {x y z} → (x ≈ x) → (y ≈ y) → (z ≈ z) → ((y + z) * x) ≈ ((y * x) + (z * x))

_DistributesOver_ : Op₂ A → Op₂ A → Set _
* DistributesOver + = (* DistributesOverˡ +) × (* DistributesOverʳ +)

_IdempotentOn_ : Op₂ A → A → Set _
_∙_ IdempotentOn x = (x ∙ x) ≈ x

Idempotent : Op₂ A → Set _
Idempotent ∙ = ∀ {x} → (x ≈ x) → ∙ IdempotentOn x

IdempotentFun : Op₁ A → Set _
IdempotentFun f = ∀ {x} → (x ≈ x) → f (f x) ≈ f x

Selective : Op₂ A → Set _
Selective _∙_ = ∀ {x y} → (x ≈ x) → (x ∙ y) ≈ x ⊎ (x ∙ y) ≈ y

_Absorbs_ : Op₂ A → Op₂ A → Set _
_∙_ Absorbs _∘_ = ∀ {x y} → (x ≈ x) → (y ≈ y) → (x ∙ (x ∘ y)) ≈ x

Absorptive : Op₂ A → Op₂ A → Set _
Absorptive ∙ ∘ = (∙ Absorbs ∘) × (∘ Absorbs ∙)

Involutive : Op₁ A → Set _
Involutive f = ∀ {x} → (x ≈ x) → f (f x) ≈ x

LeftCancellative : Op₂ A → Set _
LeftCancellative _•_ = ∀ {x y z} → (x ≈ x) → (y ≈ y) → (z ≈ z) → (x • y) ≈ (x • z) → y ≈ z

RightCancellative : Op₂ A → Set _
RightCancellative _•_ = ∀ {x y z} → (x ≈ x) → (y ≈ y) → (z ≈ z) → (y • x) ≈ (z • x) → y ≈ z

Cancellative : Op₂ A → Set _
Cancellative _•_ = (LeftCancellative _•_) × (RightCancellative _•_)

LeftCongruent : Op₂ A → Set _
LeftCongruent _∙_ = ∀ {x} → (x ≈ x) → (x ∙_) Preserves _≈_ ⟶ _≈_

RightCongruent : Op₂ A → Set _
RightCongruent _∙_ = ∀ {x} → (x ≈ x) → (_∙ x) Preserves _≈_ ⟶ _≈_
