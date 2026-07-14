------------------------------------------------------------------------
-- The Agda standard library
--
-- Relationships between properties of functions. See
-- `Function.Consequences.Propositional` for specialisations to
-- propositional equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Consequences where

open import Data.Product.Base as Product
open import Function.Base using (_∘_)
import Function.Definitions as Definitions
import Function.Definitions.Strictly as Strictly
open import Level using (Level)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive; HalfLeftAdjoint; HalfRightAdjoint; Adjoint)
open import Relation.Nullary.Negation.Core using (¬_; contraposition)

private
  variable
    a b ℓ₁ ℓ₂ : Level
    A B : Set a
    ≈₁ ≈₂ : Rel A ℓ₁
    f : A → B
    f⁻¹ : B → A



------------------------------------------------------------------------
-- Injective

module _ {≈₁ : Rel A ℓ₁} (≈₂ : Rel B ℓ₂) where

  open Definitions ≈₁ ≈₂

  contraInjective : Injective f →
                    ∀ {x y} → ¬ (≈₁ x y) → ¬ (≈₂ (f x) (f y))
  contraInjective inj = contraposition inj

------------------------------------------------------------------------
-- Inverseˡ

module _ {≈₁ : Rel A ℓ₁} {f} {f⁻¹} (≈₂ : Rel B ℓ₂) where

  open Definitions ≈₁ ≈₂

  inverseˡ⇒surjective : Inverseˡ f f⁻¹ → Surjective f
  inverseˡ⇒surjective invˡ _ = (_ , invˡ)

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) where

  open Definitions ≈₁ ≈₂

  inverseˡ⇒halfLeftAdjoint : Inverseˡ f f⁻¹ → HalfLeftAdjoint ≈₁ ≈₂ f f⁻¹
  inverseˡ⇒halfLeftAdjoint inv = inv

  halfLeftAdjoint⇒inverseˡ : HalfLeftAdjoint ≈₁ ≈₂ f f⁻¹ → Inverseˡ f f⁻¹
  halfLeftAdjoint⇒inverseˡ adj = adj

------------------------------------------------------------------------
-- Inverseʳ

module _ {≈₁ : Rel A ℓ₁} {f⁻¹} (≈₂ : Rel B ℓ₂) where

  open Definitions ≈₁ ≈₂

  inverseʳ⇒injective : ∀ f →
                       Reflexive ≈₂ →
                       Symmetric ≈₁ →
                       Transitive ≈₁ →
                       Inverseʳ f f⁻¹ → Injective f
  inverseʳ⇒injective f refl sym trans invʳ = trans (sym (invʳ refl)) ∘ invʳ

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) where

  open Definitions ≈₁ ≈₂

  inverseʳ⇒halfRightAdjoint : Symmetric ≈₁ → Symmetric ≈₂ →
                              Inverseʳ f f⁻¹ → HalfRightAdjoint ≈₁ ≈₂ f f⁻¹
  inverseʳ⇒halfRightAdjoint sym₁ sym₂ inv = sym₁ ∘ inv ∘ sym₂

  halfRightAdjoint⇒inverseʳ : Symmetric ≈₁ → Symmetric ≈₂ →
                              HalfRightAdjoint ≈₁ ≈₂ f f⁻¹ → Inverseʳ f f⁻¹
  halfRightAdjoint⇒inverseʳ sym₁ sym₂ adj = sym₁ ∘ adj ∘ sym₂

------------------------------------------------------------------------
-- Inverseᵇ

module _ {≈₁ : Rel A ℓ₁} {f} {f⁻¹} (≈₂ : Rel B ℓ₂) where

  open Definitions ≈₁ ≈₂

  inverseᵇ⇒bijective : Reflexive ≈₂ → Symmetric ≈₁ → Transitive ≈₁ →
                       Inverseᵇ f f⁻¹ → Bijective f
  inverseᵇ⇒bijective refl sym trans (invˡ , invʳ) =
    (inverseʳ⇒injective ≈₂ f refl sym trans invʳ , inverseˡ⇒surjective ≈₂ invˡ)

module _ (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) where

  open Definitions ≈₁ ≈₂

  inverseᵇ⇒adjoint : Symmetric ≈₁ → Symmetric ≈₂ →
                     Inverseᵇ f f⁻¹ → Adjoint ≈₁ ≈₂ f f⁻¹
  inverseᵇ⇒adjoint sym₁ sym₂ (invˡ , invʳ) = invˡ , sym₁ ∘ invʳ ∘ sym₂

  adjoint⇒inverseᵇ : Symmetric ≈₁ → Symmetric ≈₂ →
                     Adjoint ≈₁ ≈₂ f f⁻¹ → Inverseᵇ f f⁻¹
  adjoint⇒inverseᵇ sym₁ sym₂ (adjˡ , adjʳ) = adjˡ , sym₁ ∘ adjʳ ∘ sym₂

------------------------------------------------------------------------
-- StrictlySurjective

module _ {≈₁ : Rel A ℓ₁} {f} (≈₂ : Rel B ℓ₂) where

  open Definitions ≈₁ ≈₂

  surjective⇒strictlySurjective : Reflexive ≈₁ →
                                  Surjective f → Strictly.Surjective ≈₂ f
  surjective⇒strictlySurjective refl surj = Product.map₂ (λ v → v refl) ∘ surj

  strictlySurjective⇒surjective : Transitive ≈₂ → Congruent f →
                                  Strictly.Surjective ≈₂ f → Surjective f
  strictlySurjective⇒surjective trans cong surj x =
    Product.map₂ (λ fy≈x z≈y → trans (cong z≈y) fy≈x) (surj x)

------------------------------------------------------------------------
-- StrictlyInverseˡ

module _ {f} {f⁻¹} (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) where

  open Definitions ≈₁ ≈₂

  inverseˡ⇒strictlyInverseˡ : Reflexive ≈₁ →
                              Inverseˡ f f⁻¹ → Strictly.Inverseˡ ≈₂ f f⁻¹
  inverseˡ⇒strictlyInverseˡ refl sinv _ = sinv refl

module _ {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} {f} {f⁻¹} where

  open Definitions ≈₁ ≈₂

  strictlyInverseˡ⇒inverseˡ : Transitive ≈₂ → Congruent f →
                              Strictly.Inverseˡ ≈₂ f f⁻¹ → Inverseˡ f f⁻¹
  strictlyInverseˡ⇒inverseˡ trans cong sinv {x} y≈f⁻¹x =
    trans (cong y≈f⁻¹x) (sinv x)

------------------------------------------------------------------------
-- StrictlyInverseʳ

module _ {f} {f⁻¹} (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂) where

  open Definitions ≈₁ ≈₂

  inverseʳ⇒strictlyInverseʳ : Reflexive ≈₂ →
                              Inverseʳ f f⁻¹ → Strictly.Inverseʳ ≈₁ f f⁻¹
  inverseʳ⇒strictlyInverseʳ = inverseˡ⇒strictlyInverseˡ ≈₂ ≈₁

module _ {≈₁ : Rel A ℓ₁} {≈₂ : Rel B ℓ₂} {f⁻¹} {f} where

  open Definitions ≈₁ ≈₂

  strictlyInverseʳ⇒inverseʳ : Transitive ≈₁ → Definitions.Congruent ≈₂ ≈₁ f⁻¹ →
                              Strictly.Inverseʳ ≈₁ f f⁻¹ → Inverseʳ f f⁻¹
  strictlyInverseʳ⇒inverseʳ trans = strictlyInverseˡ⇒inverseˡ trans
