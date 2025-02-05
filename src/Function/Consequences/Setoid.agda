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
open import Relation.Nullary.Negation.Core

import Function.Consequences as C

private
  open module S = Setoid S using () renaming (Carrier to A; _≈_ to ≈₁)
  open module T = Setoid T using () renaming (Carrier to B; _≈_ to ≈₂)

  variable
    to f : A → B
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

------------------------------------------------------------------------
-- Inverseʳ

inverseʳ⇒injective : ∀ f → Inverseʳ ≈₁ ≈₂ f f⁻¹ → Injective ≈₁ ≈₂ f
inverseʳ⇒injective f = C.inverseʳ⇒injective ≈₂ f T.refl S.sym S.trans

------------------------------------------------------------------------
-- Inverseᵇ

inverseᵇ⇒bijective : Inverseᵇ ≈₁ ≈₂ f f⁻¹ → Bijective ≈₁ ≈₂ f
inverseᵇ⇒bijective = C.inverseᵇ⇒bijective ≈₂ T.refl S.sym S.trans

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

------------------------------------------------------------------------
-- Section

module Section (surj :  Surjective ≈₁ ≈₂ to) where

  private module Sf = C.Section ≈₂ surj

  open Sf public using (from; inverseˡ)

  strictlySurjective : StrictlySurjective ≈₂ to
  strictlySurjective = Sf.strictlySurjective S.refl

  strictlyInverseˡ : StrictlyInverseˡ ≈₂ to from
  strictlyInverseˡ = Sf.strictlyInverseˡ S.refl

  injective : Injective ≈₂ ≈₁ from
  injective = Sf.injective S.refl T.sym T.trans

  module _ (inj : Injective ≈₁ ≈₂ to) where

    cong : Congruent ≈₂ ≈₁ from
    cong = Sf.cong inj S.refl T.sym T.trans

    inverseʳ : Inverseʳ ≈₁ ≈₂ to from
    inverseʳ = Sf.inverseʳ inj S.refl T.trans

    strictlyInverseʳ : StrictlyInverseʳ ≈₁ to from
    strictlyInverseʳ = Sf.strictlyInverseʳ inj S.refl T.refl T.trans

    surjective : Surjective ≈₂ ≈₁ from
    surjective = Sf.surjective inj S.refl T.trans

    bijective : Bijective ≈₂ ≈₁ from
    bijective = Sf.bijective inj S.refl T.sym T.trans
