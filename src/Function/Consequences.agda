------------------------------------------------------------------------
-- The Agda standard library
--
-- Relationships between properties of functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Consequences where

open import Data.Product.Base using (_,_)
open import Function.Definitions
open import Level using (Level)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Nullary.Negation.Core using (¬_; contraposition)

private
  variable
    a b ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) {f f⁻¹} where

  inverseˡ⇒surjective : Inverseˡ ≈₁ ≈₂ f f⁻¹ → Surjective ≈₁ ≈₂ f
  inverseˡ⇒surjective invˡ y = (f⁻¹ y , invˡ y)

  inverseʳ⇒surjective : Inverseʳ ≈₁ ≈₂ f f⁻¹ → Surjective ≈₂ ≈₁ f⁻¹
  inverseʳ⇒surjective invʳ y = (f y , invʳ y)

module _ (From : Setoid a ℓ₁) {≈₂ : Rel B ℓ₂} where

  open Setoid From using () renaming (Carrier to A; _≈_ to ≈₁)

  inverseʳ⇒injective : ∀ {f f⁻¹} → Congruent ≈₂ ≈₁ f⁻¹ →
                       Inverseʳ ≈₁ ≈₂ f f⁻¹ → Injective ≈₁ ≈₂ f
  inverseʳ⇒injective {f} {f⁻¹} cong₂ invʳ {x} {y} x≈y = begin
    x         ≈˘⟨ invʳ x ⟩
    f⁻¹ (f x) ≈⟨  cong₂ x≈y ⟩
    f⁻¹ (f y) ≈⟨  invʳ y ⟩
    y         ∎
    where open SetoidReasoning From

  inverseᵇ⇒bijective : ∀ {f f⁻¹} → Congruent ≈₂ ≈₁ f⁻¹ → Inverseᵇ ≈₁ ≈₂ f f⁻¹ → Bijective ≈₁ ≈₂ f
  inverseᵇ⇒bijective cong₂ (invˡ , invʳ) =
    (inverseʳ⇒injective cong₂ invʳ , inverseˡ⇒surjective ≈₁ ≈₂ invˡ)

module _
  {f : A → B} (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂)
  where

  contraInjective : Injective _≈₁_ _≈₂_ f →
                    ∀ {x y} → ¬ (x ≈₁ y) → ¬ (f x ≈₂ f y)
  contraInjective inj p = contraposition inj p
