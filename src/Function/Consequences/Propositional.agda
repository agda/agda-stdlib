------------------------------------------------------------------------
-- The Agda standard library
--
-- Relationships between properties of functions where the equality
-- over both the domain and codomain is assumed to be _≡_
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Consequences.Propositional where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (setoid)
open import Function.Definitions

import Function.Consequences as Consequences
import Function.Consequences.Setoid as SetoidConsequences

------------------------------------------------------------------------
-- Re-export basic properties

open Consequences public
  using (contraInjective)

------------------------------------------------------------------------
-- Re-export setoid properties

module _ {a b} {A : Set a} {B : Set b} where

  open module App = SetoidConsequences (setoid A) (setoid B) public
    hiding
    ( strictlySurjective⇒surjective
    ; strictlyInverseˡ⇒inverseˡ
    ; strictlyInverseʳ⇒inverseʳ
    ; contraInjective
    )

------------------------------------------------------------------------
-- Properties that rely on congruence

  private
    variable
      f : A → B
      f⁻¹ : B → A

  strictlySurjective⇒surjective : StrictlySurjective _≡_ f →
                                   Surjective _≡_ _≡_ f
  strictlySurjective⇒surjective =
    App.strictlySurjective⇒surjective (cong _)


  strictlyInverseˡ⇒inverseˡ : ∀ f → StrictlyInverseˡ _≡_ f f⁻¹ →
                              Inverseˡ _≡_ _≡_ f f⁻¹
  strictlyInverseˡ⇒inverseˡ f =
    App.strictlyInverseˡ⇒inverseˡ (cong _)


  strictlyInverseʳ⇒inverseʳ : ∀ f → StrictlyInverseʳ _≡_ f f⁻¹ →
                              Inverseʳ _≡_ _≡_ f f⁻¹
  strictlyInverseʳ⇒inverseʳ f =
    App.strictlyInverseʳ⇒inverseʳ (cong _)
