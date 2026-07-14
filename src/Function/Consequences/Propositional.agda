------------------------------------------------------------------------
-- The Agda standard library
--
-- Relationships between properties of functions where the equality
-- over both the domain and codomain is assumed to be _≡_
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Consequences.Propositional
  {a b} {A : Set a} {B : Set b}
  where

open import Data.Product.Base using (_,_)
import Function.Definitions as Definitions
  using (Inverseˡ; Inverseʳ; Surjective)
import Function.Definitions.Strictly as Strictly
  using (Surjective; Inverseˡ; Inverseʳ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Properties
  using (setoid)
open import Relation.Nullary.Negation.Core using (contraposition)


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

open Definitions (_≡_ {A = A}) (_≡_ {A = B})

strictlySurjective⇒surjective : Strictly.Surjective _≡_ f →
                                Surjective f
strictlySurjective⇒surjective surj y =
  let x , fx≡y = surj y in x , λ where refl → fx≡y

strictlyInverseˡ⇒inverseˡ : ∀ f → Strictly.Inverseˡ _≡_ f f⁻¹ →
                            Inverseˡ f f⁻¹
strictlyInverseˡ⇒inverseˡ _ inv refl = inv _

strictlyInverseʳ⇒inverseʳ : ∀ f → Strictly.Inverseʳ _≡_ f f⁻¹ →
                            Inverseʳ f f⁻¹
strictlyInverseʳ⇒inverseʳ _ inv refl = inv _

