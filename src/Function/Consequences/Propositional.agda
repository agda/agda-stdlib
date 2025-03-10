------------------------------------------------------------------------
-- The Agda standard library
--
-- Relationships between properties of functions where the equality
-- over both the domain and codomain is assumed to be _≡_
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Consequences.Propositional
  {a b} {A : Set a} {B : Set b}
  where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (setoid)
import Function.Definitions as Definitions
open import Function.Definitions.Strict as Strict
open import Relation.Nullary.Negation.Core using (contraposition)

import Function.Consequences.Setoid (setoid A) (setoid B) as Setoid

------------------------------------------------------------------------
-- Re-export setoid properties

open Setoid public
  hiding
  ( strictlySurjective⇒surjective
  ; strictlyInverseˡ⇒inverseˡ
  ; strictlyInverseʳ⇒inverseʳ
  )

------------------------------------------------------------------------
-- Properties that rely on congruence

private
  variable
    f : A → B
    f⁻¹ : B → A

open Definitions (_≡_ {A = A}) (_≡_ {A = B})

strictlySurjective⇒surjective : StrictlySurjective _≡_ f →
                                 Surjective f
strictlySurjective⇒surjective =
 Setoid.strictlySurjective⇒surjective (cong _)

strictlyInverseˡ⇒inverseˡ : ∀ f → StrictlyInverseˡ _≡_ f f⁻¹ →
                            Inverseˡ f f⁻¹
strictlyInverseˡ⇒inverseˡ f =
  Setoid.strictlyInverseˡ⇒inverseˡ (cong _)

strictlyInverseʳ⇒inverseʳ : ∀ f → StrictlyInverseʳ _≡_ f f⁻¹ →
                            Inverseʳ f f⁻¹
strictlyInverseʳ⇒inverseʳ f =
  Setoid.strictlyInverseʳ⇒inverseʳ (cong _)
