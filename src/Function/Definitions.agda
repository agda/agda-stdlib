------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for types of functions.
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from `Function`.

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Definitions where

open import Data.Product.Base using (∃; _×_)
open import Level using (Level)
open import Relation.Binary.Core using (Rel)

private
  variable
    a ℓ₁ ℓ₂ : Level
    A B : Set a

------------------------------------------------------------------------
-- Basic definitions

module _
  (_≈₁_ : Rel A ℓ₁) -- Equality over the domain
  (_≈₂_ : Rel B ℓ₂) -- Equality over the codomain
  where

  Congruent : (A → B) → Set _
  Congruent f = ∀ {x y} → x ≈₁ y → f x ≈₂ f y

  Injective : (A → B) → Set _
  Injective f = ∀ {x y} → f x ≈₂ f y → x ≈₁ y

  Surjective : (A → B) → Set _
  Surjective f = ∀ y → ∃ λ x → ∀ {z} → z ≈₁ x → f z ≈₂ y

  Bijective : (A → B) → Set _
  Bijective f = Injective f × Surjective f

  Inverseˡ : (A → B) → (B → A) → Set _
  Inverseˡ f g = ∀ {x y} → y ≈₁ g x → f y ≈₂ x

  Inverseʳ : (A → B) → (B → A) → Set _
  Inverseʳ f g = ∀ {x y} → y ≈₂ f x → g y ≈₁ x

  Inverseᵇ : (A → B) → (B → A) → Set _
  Inverseᵇ f g = Inverseˡ f g × Inverseʳ f g

------------------------------------------------------------------------
-- Strict definitions

-- These are often easier to use once but much harder to compose and
-- reason about.

StrictlySurjective : Rel B ℓ₂ → (A → B) → Set _
StrictlySurjective _≈₂_ f = ∀ y → ∃ λ x → f x ≈₂ y

StrictlyInverseˡ : Rel B ℓ₂ → (A → B) → (B → A) → Set _
StrictlyInverseˡ _≈₂_ f g = ∀ y → f (g y) ≈₂ y

StrictlyInverseʳ : Rel A ℓ₁ → (A → B) → (B → A) → Set _
StrictlyInverseʳ _≈₁_ f g = ∀ x → g (f x) ≈₁ x
