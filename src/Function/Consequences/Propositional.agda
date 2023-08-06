------------------------------------------------------------------------
-- The Agda standard library
--
-- Relationships between properties of functions where the equality
-- over both the domain and codomain is assumed to be _≡_
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Consequences.Propositional where

open import Function.Definitions
open import Level
open import Relation.Nullary.Negation.Core using (contraposition)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; trans; cong)

import Function.Consequences as C

private
  variable
    a b ℓ₁ ℓ₂ : Level
    A B : Set a
    f f⁻¹ : A → B

------------------------------------------------------------------------
-- Injective

contraInjective : Injective _≡_ _≡_ f →
                  ∀ {x y} → x ≢ y → f x ≢ f y
contraInjective inj p = contraposition inj p

------------------------------------------------------------------------
-- Inverseˡ

inverseˡ⇒surjective : Inverseˡ _≡_ _≡_ f f⁻¹ → Surjective _≡_ _≡_ f
inverseˡ⇒surjective = C.inverseˡ⇒surjective _≡_

------------------------------------------------------------------------
-- Inverseʳ

inverseʳ⇒injective : ∀ f →
                     Inverseʳ _≡_ _≡_ f f⁻¹ →
                     Injective _≡_ _≡_ f
inverseʳ⇒injective f = C.inverseʳ⇒injective _≡_ f refl sym trans

------------------------------------------------------------------------
-- Inverseᵇ

inverseᵇ⇒bijective : Inverseᵇ _≡_ _≡_ f f⁻¹ → Bijective _≡_ _≡_ f
inverseᵇ⇒bijective = C.inverseᵇ⇒bijective _≡_ refl sym trans

------------------------------------------------------------------------
-- StrictlySurjective

surjective⇒strictlySurjective : Surjective _≡_ _≡_ f →
                                 StrictlySurjective _≡_ f
surjective⇒strictlySurjective =
  C.surjective⇒strictlySurjective _≡_ refl

strictlySurjective⇒surjective : StrictlySurjective _≡_ f →
                                 Surjective _≡_ _≡_ f
strictlySurjective⇒surjective =
  C.strictlySurjective⇒surjective trans (cong _)

------------------------------------------------------------------------
-- StrictlyInverseˡ

inverseˡ⇒strictlyInverseˡ : Inverseˡ _≡_ _≡_ f f⁻¹ →
                            StrictlyInverseˡ _≡_ f f⁻¹
inverseˡ⇒strictlyInverseˡ =
  C.inverseˡ⇒strictlyInverseˡ _≡_ _≡_ refl

strictlyInverseˡ⇒inverseˡ : ∀ f →
                            StrictlyInverseˡ _≡_ f f⁻¹ →
                            Inverseˡ _≡_ _≡_ f f⁻¹
strictlyInverseˡ⇒inverseˡ f =
  C.strictlyInverseˡ⇒inverseˡ trans (cong f)

------------------------------------------------------------------------
-- StrictlyInverseʳ

inverseʳ⇒strictlyInverseʳ : Inverseʳ _≡_ _≡_ f f⁻¹ →
                            StrictlyInverseʳ _≡_ f f⁻¹
inverseʳ⇒strictlyInverseʳ = C.inverseʳ⇒strictlyInverseʳ _≡_ _≡_ refl

strictlyInverseʳ⇒inverseʳ : ∀ f →
                            StrictlyInverseʳ _≡_ f f⁻¹ →
                            Inverseʳ _≡_ _≡_ f f⁻¹
strictlyInverseʳ⇒inverseʳ {f⁻¹ = f⁻¹} _ =
  C.strictlyInverseʳ⇒inverseʳ trans (cong f⁻¹)
