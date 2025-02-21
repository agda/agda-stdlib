------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for types of functions,
-- wrt to `_≈₁_` equality over the domain
-- and `_≈₂_` equality over the codomain.
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from `Function`.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)

module Function.Definitions
  {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂)
  where

open import Data.Product.Base using (∃; _×_)

------------------------------------------------------------------------
-- Basic definitions

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
