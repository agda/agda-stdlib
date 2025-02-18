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

open import Data.Product.Base using (_,_)
open import Function.Definitions
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Properties
  using (setoid)

------------------------------------------------------------------------
-- Re-export setoid properties

open import Function.Consequences.Setoid (setoid A) (setoid B) public
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

strictlySurjective⇒surjective : StrictlySurjective _≡_ f →
                                 Surjective _≡_ _≡_ f
strictlySurjective⇒surjective surj y =
  let x , fx≡y = surj y in x , λ where refl → fx≡y

strictlyInverseˡ⇒inverseˡ : ∀ f → StrictlyInverseˡ _≡_ f f⁻¹ →
                            Inverseˡ _≡_ _≡_ f f⁻¹
strictlyInverseˡ⇒inverseˡ _ inv refl = inv _

strictlyInverseʳ⇒inverseʳ : ∀ f → StrictlyInverseʳ _≡_ f f⁻¹ →
                            Inverseʳ _≡_ _≡_ f f⁻¹
strictlyInverseʳ⇒inverseʳ _ inv refl = inv _

