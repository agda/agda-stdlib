------------------------------------------------------------------------
-- The Agda standard library
--
-- Results concerning function extensionality for propositional equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Axiom.Extensionality.Heterogeneous where

import Axiom.Extensionality.Propositional as P
open import Function
open import Level
open import Relation.Binary.HeterogeneousEquality.Core
open import Relation.Binary.PropositionalEquality.Core

------------------------------------------------------------------------
-- Function extensionality states that if two functions are
-- propositionally equal for every input, then the functions themselves
-- must be propositionally equal.

Extensionality : (a b : Level) → Set _
Extensionality a b =
  {A : Set a} {B₁ B₂ : A → Set b}
  {f₁ : (x : A) → B₁ x} {f₂ : (x : A) → B₂ x} →
  (∀ x → B₁ x ≡ B₂ x) → (∀ x → f₁ x ≅ f₂ x) → f₁ ≅ f₂

------------------------------------------------------------------------
-- Properties

-- This form of extensionality follows from extensionality for _≡_.

≡-ext⇒≅-ext : ∀ {ℓ₁ ℓ₂} →
              P.Extensionality ℓ₁ (suc ℓ₂) →
              Extensionality ℓ₁ ℓ₂
≡-ext⇒≅-ext {ℓ₁} {ℓ₂} ext B₁≡B₂ f₁≅f₂ with ext B₁≡B₂
... | refl = ≡-to-≅ $ ext′ (≅-to-≡ ∘ f₁≅f₂)
  where
  ext′ : P.Extensionality ℓ₁ ℓ₂
  ext′ = P.lower ℓ₁ (suc ℓ₂) ext
