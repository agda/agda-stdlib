------------------------------------------------------------------------
-- The Agda standard library
--
-- Relationships between properties of functions. See
-- `Function.Consequences.Propositional` for specialisations to
-- propositional equality.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Consequences where

open import Data.Product.Base as Product
open import Function.Base using (_∘_; id)
open import Function.Definitions
open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive; HalfLeftAdjoint; HalfRightAdjoint; Adjoint)
open import Relation.Nullary.Negation.Core using (¬_; contraposition)

private
  variable
    a b ℓ₁ ℓ₂ : Level
    A B : Set a
    ≈₁ ≈₂ : Rel A ℓ₁
    f f⁻¹ : A → B

------------------------------------------------------------------------
-- Injective

contraInjective : ∀ (≈₂ : Rel B ℓ₂) → Injective ≈₁ ≈₂ f →
                  ∀ {x y} → ¬ (≈₁ x y) → ¬ (≈₂ (f x) (f y))
contraInjective _ inj p = contraposition inj p

------------------------------------------------------------------------
-- Inverseˡ

inverseˡ⇒surjective : ∀ (≈₂ : Rel B ℓ₂) →
                      Inverseˡ ≈₁ ≈₂ f f⁻¹ →
                      Surjective ≈₁ ≈₂ f
inverseˡ⇒surjective ≈₂ invˡ y = (_ , invˡ)

inverseˡ⇒halfLeftAdjoint : ∀ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) →
                           Inverseˡ ≈₁ ≈₂ f f⁻¹ →
                           HalfLeftAdjoint ≈₁ ≈₂ f f⁻¹
inverseˡ⇒halfLeftAdjoint _ _ inv = inv

halfLeftAdjoint⇒inverseˡ : ∀ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) →
                           HalfLeftAdjoint ≈₁ ≈₂ f f⁻¹ →
                           Inverseˡ ≈₁ ≈₂ f f⁻¹
halfLeftAdjoint⇒inverseˡ _ _ adj = adj

------------------------------------------------------------------------
-- Inverseʳ

inverseʳ⇒injective : ∀ (≈₂ : Rel B ℓ₂) f →
                     Reflexive ≈₂ →
                     Symmetric ≈₁ →
                     Transitive ≈₁ →
                     Inverseʳ ≈₁ ≈₂ f f⁻¹ →
                     Injective ≈₁ ≈₂ f
inverseʳ⇒injective ≈₂ f refl sym trans invʳ {x} {y} fx≈fy =
  trans (sym (invʳ refl)) (invʳ fx≈fy)

inverseʳ⇒halfRightAdjoint : ∀ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) →
                            Symmetric ≈₁ → Symmetric ≈₂ →
                            Inverseʳ ≈₁ ≈₂ f f⁻¹ →
                            HalfRightAdjoint ≈₁ ≈₂ f f⁻¹
inverseʳ⇒halfRightAdjoint _ _ sym₁ sym₂ inv = sym₁ ∘ inv ∘ sym₂

halfRightAdjoint⇒inverseʳ : ∀ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) →
                            Symmetric ≈₁ → Symmetric ≈₂ →
                            HalfRightAdjoint ≈₁ ≈₂ f f⁻¹ →
                            Inverseʳ ≈₁ ≈₂ f f⁻¹
halfRightAdjoint⇒inverseʳ _ _ sym₁ sym₂ adj = sym₁ ∘ adj ∘ sym₂

------------------------------------------------------------------------
-- Inverseᵇ

inverseᵇ⇒bijective : ∀ (≈₂ : Rel B ℓ₂) →
                     Reflexive ≈₂ →
                     Symmetric ≈₁ →
                     Transitive ≈₁ →
                     Inverseᵇ ≈₁ ≈₂ f f⁻¹ →
                     Bijective ≈₁ ≈₂ f
inverseᵇ⇒bijective {f = f} ≈₂ refl sym trans (invˡ , invʳ) =
  (inverseʳ⇒injective ≈₂ f refl sym trans invʳ , inverseˡ⇒surjective ≈₂ invˡ)

inverseᵇ⇒adjoint : ∀ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) →
                   Symmetric ≈₁ → Symmetric ≈₂ →
                   Inverseᵇ ≈₁ ≈₂ f f⁻¹ → Adjoint ≈₁ ≈₂ f f⁻¹
inverseᵇ⇒adjoint _ _ sym₁ sym₂ (invˡ , invʳ) = invˡ , sym₁ ∘ invʳ ∘ sym₂

adjoint⇒inverseᵇ : ∀ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) →
                   Symmetric ≈₁ → Symmetric ≈₂ →
                   Adjoint ≈₁ ≈₂ f f⁻¹ → Inverseᵇ ≈₁ ≈₂ f f⁻¹
adjoint⇒inverseᵇ _ _ sym₁ sym₂ (adjˡ , adjʳ) = adjˡ , sym₁ ∘ adjʳ ∘ sym₂

------------------------------------------------------------------------
-- StrictlySurjective

surjective⇒strictlySurjective : ∀ (≈₂ : Rel B ℓ₂) →
                                 Reflexive ≈₁ →
                                 Surjective ≈₁ ≈₂ f →
                                 StrictlySurjective ≈₂ f
surjective⇒strictlySurjective _ refl surj x =
  Product.map₂ (λ v → v refl) (surj x)

strictlySurjective⇒surjective : Transitive ≈₂ →
                                 Congruent ≈₁ ≈₂ f →
                                 StrictlySurjective ≈₂ f →
                                 Surjective ≈₁ ≈₂ f
strictlySurjective⇒surjective trans cong surj x =
  Product.map₂ (λ fy≈x z≈y → trans (cong z≈y) fy≈x) (surj x)

------------------------------------------------------------------------
-- StrictlyInverseˡ

inverseˡ⇒strictlyInverseˡ : ∀ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) →
                            Reflexive ≈₁ →
                            Inverseˡ ≈₁ ≈₂ f f⁻¹ →
                            StrictlyInverseˡ ≈₂ f f⁻¹
inverseˡ⇒strictlyInverseˡ _ _ refl sinv x = sinv refl

strictlyInverseˡ⇒inverseˡ : Transitive ≈₂ →
                            Congruent ≈₁ ≈₂ f →
                            StrictlyInverseˡ ≈₂ f f⁻¹ →
                            Inverseˡ ≈₁ ≈₂ f f⁻¹
strictlyInverseˡ⇒inverseˡ trans cong sinv {x} y≈f⁻¹x =
  trans (cong y≈f⁻¹x) (sinv x)

------------------------------------------------------------------------
-- StrictlyInverseʳ

inverseʳ⇒strictlyInverseʳ : ∀ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) →
                            Reflexive ≈₂ →
                            Inverseʳ ≈₁ ≈₂ f f⁻¹ →
                            StrictlyInverseʳ ≈₁ f f⁻¹
inverseʳ⇒strictlyInverseʳ _ _ refl sinv x = sinv refl

strictlyInverseʳ⇒inverseʳ : Transitive ≈₁ →
                            Congruent ≈₂ ≈₁ f⁻¹ →
                            StrictlyInverseʳ ≈₁ f f⁻¹ →
                            Inverseʳ ≈₁ ≈₂ f f⁻¹
strictlyInverseʳ⇒inverseʳ trans cong sinv {x} y≈f⁻¹x =
  trans (cong y≈f⁻¹x) (sinv x)
