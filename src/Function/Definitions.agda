------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for types of functions.
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from `Function`.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Function.Definitions
  {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
  (_≈₁_ : Rel A ℓ₁) -- Equality over the domain
  (_≈₂_ : Rel B ℓ₂) -- Equality over the codomain
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
  using (Inverseˡ)

open Core₁ _≈₁_ public
  using (Inverseʳ)

Inverseᵇ : (A → B) → (B → A) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
Inverseᵇ f g = Inverseˡ f g × Inverseʳ f g
