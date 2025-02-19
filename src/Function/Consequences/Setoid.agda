------------------------------------------------------------------------
-- The Agda standard library
--
-- Relationships between properties of functions where the equality
-- over both the domain and codomain are assumed to be setoids.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Function.Consequences.Setoid
  {a b ℓ₁ ℓ₂}
  (S : Setoid a ℓ₁)
  (T : Setoid b ℓ₂)
  where

open import Function.Definitions
open import Relation.Binary.Definitions
  using (HalfLeftAdjoint; HalfRightAdjoint; Adjoint)
open import Relation.Nullary.Negation.Core

import Function.Consequences as C

private
  open module S = Setoid S using () renaming (Carrier to A; _≈_ to ≈₁; sym to sym₁)
  open module T = Setoid T using () renaming (Carrier to B; _≈_ to ≈₂; sym to sym₂)

  variable
    f : A → B
    f⁻¹ : B → A

------------------------------------------------------------------------
-- Injective

contraInjective : Injective ≈₁ ≈₂ f →
                  ∀ {x y} → ¬ (≈₁ x y) → ¬ (≈₂ (f x) (f y))
contraInjective = C.contraInjective ≈₂

------------------------------------------------------------------------
-- Inverseˡ

inverseˡ⇒surjective : Inverseˡ ≈₁ ≈₂ f f⁻¹ → Surjective ≈₁ ≈₂ f
inverseˡ⇒surjective = C.inverseˡ⇒surjective ≈₂

inverseˡ⇒halfLeftAdjoint : Inverseˡ ≈₁ ≈₂ f f⁻¹ → HalfLeftAdjoint ≈₁ ≈₂ f f⁻¹
inverseˡ⇒halfLeftAdjoint = C.inverseˡ⇒halfLeftAdjoint

halfLeftAdjoint⇒inverseˡ : HalfLeftAdjoint ≈₁ ≈₂ f f⁻¹ → Inverseˡ ≈₁ ≈₂ f f⁻¹
halfLeftAdjoint⇒inverseˡ = C.halfLeftAdjoint⇒inverseˡ

------------------------------------------------------------------------
-- Inverseʳ

inverseʳ⇒injective : ∀ f → Inverseʳ ≈₁ ≈₂ f f⁻¹ → Injective ≈₁ ≈₂ f
inverseʳ⇒injective f = C.inverseʳ⇒injective ≈₂ f T.refl S.sym S.trans

inverseʳ⇒halfRightAdjoint : Inverseʳ ≈₁ ≈₂ f f⁻¹ → HalfRightAdjoint ≈₁ ≈₂ f f⁻¹
inverseʳ⇒halfRightAdjoint = C.inverseʳ⇒halfRightAdjoint sym₁ sym₂

halfRightAdjoint⇒inverseʳ : HalfRightAdjoint ≈₁ ≈₂ f f⁻¹ → Inverseʳ ≈₁ ≈₂ f f⁻¹
halfRightAdjoint⇒inverseʳ = C.halfRightAdjoint⇒inverseʳ sym₁ sym₂

------------------------------------------------------------------------
-- Inverseᵇ

inverseᵇ⇒bijective : Inverseᵇ ≈₁ ≈₂ f f⁻¹ → Bijective ≈₁ ≈₂ f
inverseᵇ⇒bijective = C.inverseᵇ⇒bijective ≈₂ T.refl S.sym S.trans

inverseᵇ⇒adjoint : Inverseᵇ ≈₁ ≈₂ f f⁻¹ → Adjoint ≈₁ ≈₂ f f⁻¹
inverseᵇ⇒adjoint = C.inverseᵇ⇒adjoint sym₁ sym₂

adjoint⇒inverseᵇ : Adjoint ≈₁ ≈₂ f f⁻¹ → Inverseᵇ ≈₁ ≈₂ f f⁻¹
adjoint⇒inverseᵇ = C.adjoint⇒inverseᵇ sym₁ sym₂

------------------------------------------------------------------------
-- StrictlySurjective

surjective⇒strictlySurjective : Surjective ≈₁ ≈₂ f →
                                 StrictlySurjective ≈₂ f
surjective⇒strictlySurjective =
  C.surjective⇒strictlySurjective ≈₂ S.refl

strictlySurjective⇒surjective : Congruent ≈₁ ≈₂ f →
                                 StrictlySurjective ≈₂ f →
                                 Surjective ≈₁ ≈₂ f
strictlySurjective⇒surjective =
  C.strictlySurjective⇒surjective T.trans

------------------------------------------------------------------------
-- StrictlyInverseˡ

inverseˡ⇒strictlyInverseˡ : Inverseˡ ≈₁ ≈₂ f f⁻¹ →
                            StrictlyInverseˡ ≈₂ f f⁻¹
inverseˡ⇒strictlyInverseˡ = C.inverseˡ⇒strictlyInverseˡ ≈₁ ≈₂ S.refl

strictlyInverseˡ⇒inverseˡ : Congruent ≈₁ ≈₂ f →
                            StrictlyInverseˡ ≈₂ f f⁻¹ →
                            Inverseˡ ≈₁ ≈₂ f f⁻¹
strictlyInverseˡ⇒inverseˡ = C.strictlyInverseˡ⇒inverseˡ T.trans

------------------------------------------------------------------------
-- StrictlyInverseʳ

inverseʳ⇒strictlyInverseʳ : Inverseʳ ≈₁ ≈₂ f f⁻¹ →
                            StrictlyInverseʳ ≈₁ f f⁻¹
inverseʳ⇒strictlyInverseʳ = C.inverseʳ⇒strictlyInverseʳ ≈₁ ≈₂ T.refl

strictlyInverseʳ⇒inverseʳ : Congruent ≈₂ ≈₁ f⁻¹ →
                            StrictlyInverseʳ ≈₁ f f⁻¹ →
                            Inverseʳ ≈₁ ≈₂ f f⁻¹
strictlyInverseʳ⇒inverseʳ = C.strictlyInverseʳ⇒inverseʳ S.trans
