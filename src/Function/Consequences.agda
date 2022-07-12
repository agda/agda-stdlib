------------------------------------------------------------------------
-- The Agda standard library
--
-- Relationships between properties of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Consequences where

open import Data.Product
open import Function using (_∘_; flip)
open import Function.Definitions
open import Level
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation.Core using (contraposition)

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

∘-cong : ∀ {f} {g} {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} →
          Congruent ≈₁ ≈₁ f → Congruent ≈₁ ≈₂ g → Congruent ≈₁ ≈₂ (g ∘ f)
∘-cong f-cong g-cong = g-cong ∘ f-cong
-- ∘-cong = flip _∘_  -- Yields implicit/explicit function type error.

∘-cong₂ : ∀ {f} {g} {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} →
          Congruent ≈₁ ≈₁ f → Congruent₂ ≈₁ ≈₁ ≈₂ g → Congruent₂ ≈₁ ≈₁ ≈₂ (g ∘ f)
∘-cong₂ f-cong g-cong₂ = g-cong₂ ∘ f-cong

module _ (To : Setoid b ℓ₂) {≈₁ : Rel A ℓ₁} where

  open Setoid To using () renaming (Carrier to B; _≈_ to ≈₂)

  flip-cong₂ : ∀ {f} → Congruent₂ ≈₁ ≈₁ ≈₂ f → Congruent₂ ≈₁ ≈₁ ≈₂ (flip f)
  flip-cong₂ {f} f-cong₂ {x} {y} {w} {z} x≈y w≈z = begin
    flip f x w ≡⟨⟩
    f w x      ≈⟨ f-cong₂ w≈z x≈y ⟩
    f z y      ≡⟨⟩
    flip f y z ∎
    where open SetoidReasoning To
