------------------------------------------------------------------------
-- The Agda standard library
--
-- Relationships between properties of functions where the equality
-- over both the domain and codomain are assumed to be setoids.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Function.Consequences.Setoid
  {a b ℓ₁ ℓ₂}
  (S : Setoid a ℓ₁)
  (T : Setoid b ℓ₂)
  where

import Function.Consequences as C
import Function.Definitions as Definitions
import Function.Definitions.Strictly as Strictly
open import Relation.Binary.Definitions
  using (HalfLeftAdjoint; HalfRightAdjoint; Adjoint)
open import Relation.Nullary.Negation.Core using (¬_)


private
  open module S = Setoid S using () renaming (Carrier to A; _≈_ to ≈₁; sym to sym₁)
  open module T = Setoid T using () renaming (Carrier to B; _≈_ to ≈₂; sym to sym₂)

  variable
    f : A → B
    f⁻¹ : B → A
    x y : A



open Definitions ≈₁ ≈₂


------------------------------------------------------------------------
-- Injective

contraInjective : Injective f →
                  ∀ {x y} → ¬ (≈₁ x y) → ¬ (≈₂ (f x) (f y))
contraInjective = C.contraInjective ≈₂

------------------------------------------------------------------------
-- Inverseˡ

inverseˡ⇒surjective : Inverseˡ f f⁻¹ → Surjective f
inverseˡ⇒surjective = C.inverseˡ⇒surjective ≈₂

inverseˡ⇒halfLeftAdjoint : Inverseˡ f f⁻¹ → HalfLeftAdjoint ≈₁ ≈₂ f f⁻¹
inverseˡ⇒halfLeftAdjoint = C.inverseˡ⇒halfLeftAdjoint ≈₁ ≈₂

halfLeftAdjoint⇒inverseˡ : HalfLeftAdjoint ≈₁ ≈₂ f f⁻¹ → Inverseˡ f f⁻¹
halfLeftAdjoint⇒inverseˡ = C.halfLeftAdjoint⇒inverseˡ ≈₁ ≈₂

------------------------------------------------------------------------
-- Inverseʳ

inverseʳ⇒injective : ∀ f → Inverseʳ f f⁻¹ → Injective f
inverseʳ⇒injective f = C.inverseʳ⇒injective ≈₂ f T.refl S.sym S.trans

inverseʳ⇒halfRightAdjoint : Inverseʳ f f⁻¹ → HalfRightAdjoint ≈₁ ≈₂ f f⁻¹
inverseʳ⇒halfRightAdjoint = C.inverseʳ⇒halfRightAdjoint ≈₁ ≈₂ sym₁ sym₂

halfRightAdjoint⇒inverseʳ : HalfRightAdjoint ≈₁ ≈₂ f f⁻¹ → Inverseʳ f f⁻¹
halfRightAdjoint⇒inverseʳ = C.halfRightAdjoint⇒inverseʳ ≈₁ ≈₂ sym₁ sym₂

------------------------------------------------------------------------
-- Inverseᵇ

inverseᵇ⇒bijective : Inverseᵇ f f⁻¹ → Bijective f
inverseᵇ⇒bijective = C.inverseᵇ⇒bijective ≈₂ T.refl S.sym S.trans

inverseᵇ⇒adjoint : Inverseᵇ f f⁻¹ → Adjoint ≈₁ ≈₂ f f⁻¹
inverseᵇ⇒adjoint = C.inverseᵇ⇒adjoint ≈₁ ≈₂ sym₁ sym₂

adjoint⇒inverseᵇ : Adjoint ≈₁ ≈₂ f f⁻¹ → Inverseᵇ f f⁻¹
adjoint⇒inverseᵇ = C.adjoint⇒inverseᵇ ≈₁ ≈₂ sym₁ sym₂

------------------------------------------------------------------------
-- Strictly.Surjective

surjective⇒strictlySurjective : Surjective f → Strictly.Surjective ≈₂ f
surjective⇒strictlySurjective =
  C.surjective⇒strictlySurjective ≈₂ S.refl

strictlySurjective⇒surjective : Congruent f →
                                Strictly.Surjective ≈₂ f → Surjective f
strictlySurjective⇒surjective =
  C.strictlySurjective⇒surjective ≈₂ T.trans

------------------------------------------------------------------------
-- Strictly.Inverseˡ

inverseˡ⇒strictlyInverseˡ : Inverseˡ f f⁻¹ →
                            Strictly.Inverseˡ ≈₂ f f⁻¹
inverseˡ⇒strictlyInverseˡ = C.inverseˡ⇒strictlyInverseˡ ≈₁ ≈₂ S.refl

strictlyInverseˡ⇒inverseˡ : Congruent f →
                            Strictly.Inverseˡ ≈₂ f f⁻¹ → Inverseˡ f f⁻¹
strictlyInverseˡ⇒inverseˡ = C.strictlyInverseˡ⇒inverseˡ T.trans

------------------------------------------------------------------------
-- Strictly.Inverseʳ

inverseʳ⇒strictlyInverseʳ : Inverseʳ f f⁻¹ →
                            Strictly.Inverseʳ ≈₁ f f⁻¹
inverseʳ⇒strictlyInverseʳ = C.inverseʳ⇒strictlyInverseʳ ≈₁ ≈₂ T.refl

strictlyInverseʳ⇒inverseʳ : Definitions.Congruent ≈₂ ≈₁ f⁻¹ →
                            Strictly.Inverseʳ ≈₁ f f⁻¹ → Inverseʳ f f⁻¹
strictlyInverseʳ⇒inverseʳ = C.strictlyInverseʳ⇒inverseʳ S.trans
