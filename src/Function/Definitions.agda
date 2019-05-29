------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for types of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Function.Definitions
  {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂)
  where

open import Data.Product using (∃; _×_)
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Definitions

Congruent : (A → B) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
Congruent f = ∀ {x y} → x ≈₁ y → f x ≈₂ f y

Injective : (A → B) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
Injective f = ∀ {x y} → f x ≈₂ f y → x ≈₁ y

Surjective : (A → B) → Set (a ⊔ b ⊔ ℓ₂)
Surjective f = ∀ x → ∃ λ y → y ≈₂ f x

Bijective : (A → B) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
Bijective f = Injective f × Surjective f

LeftInverses : (A → B) → (B → A) → Set (b ⊔ ℓ₂)
LeftInverses f g = ∀ x → f (g x) ≈₂ x

RightInverses : (A → B) → (B → A) → Set (a ⊔ ℓ₁)
RightInverses f g = ∀ x → g (f x) ≈₁ x

Inverses : (A → B) → (B → A) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
Inverses f g = LeftInverses f g × RightInverses f g
