------------------------------------------------------------------------
-- The Agda standard library
--
-- Relationships between properties of functions where the equality
-- over both the domain and codomain is assumed to be _≡_
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Consequences.Propositional
  {a b} {A : Set a} {B : Set b} where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (setoid)
open import Function.Definitions

import Function.Consequences.Setoid (setoid A) (setoid B) as SetoidConsequences

private
  variable
    f : A → B
    f⁻¹ : B → A
    
------------------------------------------------------------------------
-- Re-export setoid properties

open SetoidConsequences public
  hiding
  ( strictlySurjective⇒surjective
  ; strictlyInverseˡ⇒inverseˡ
  ; strictlyInverseʳ⇒inverseʳ
  )

------------------------------------------------------------------------
-- Properties that rely on congruence

strictlySurjective⇒surjective : StrictlySurjective _≡_ f →
                                 Surjective _≡_ _≡_ f
strictlySurjective⇒surjective =
  SetoidConsequences.strictlySurjective⇒surjective (cong _)


strictlyInverseˡ⇒inverseˡ : ∀ f → StrictlyInverseˡ _≡_ f f⁻¹ →
                            Inverseˡ _≡_ _≡_ f f⁻¹
strictlyInverseˡ⇒inverseˡ f =
  SetoidConsequences.strictlyInverseˡ⇒inverseˡ (cong _)


strictlyInverseʳ⇒inverseʳ : ∀ f → StrictlyInverseʳ _≡_ f f⁻¹ →
                            Inverseʳ _≡_ _≡_ f f⁻¹
strictlyInverseʳ⇒inverseʳ f =
  SetoidConsequences.strictlyInverseʳ⇒inverseʳ (cong _)
