------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for types of functions.
------------------------------------------------------------------------

-- These definitions should usually be accessed from `Function`.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Function.Definitions
  {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂)
  where

open import Data.Product using (∃; _×_)
import Function.Definitions.Core1 as Core₁
import Function.Definitions.Core2 as Core₂
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Definitions

Congruent : (A → B) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
Congruent f = ∀ {x y} → x ≈₁ y → f x ≈₂ f y

Injective : (A → B) → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
Injective f = ∀ {x y} → f x ≈₂ f y → x ≈₁ y

open Core₂ _≈₂_ public
  using (Surjective)

Bijective : (A → B) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
Bijective f = Injective f × Surjective f

open Core₂ _≈₂_ public
  using (LeftInverses)

open Core₁ _≈₁_ public
  using (RightInverses)

Inverses : (A → B) → (B → A) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
Inverses f g = LeftInverses f g × RightInverses f g
