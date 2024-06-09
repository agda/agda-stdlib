------------------------------------------------------------------------
-- The Agda standard library
--
-- The basic code for equational reasoning with a non-reflexive relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Function.Base using (case_of_)
open import Level using (_⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Transitive; Trans; Reflexive)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Reasoning.Syntax


module Relation.Binary.Reasoning.Base.Partial
  {a ℓ} {A : Set a} (_∼_ : Rel A ℓ) (trans : Transitive _∼_)
  where

------------------------------------------------------------------------
-- Definition of "related to"

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

infix  4 _IsRelatedTo_

data _IsRelatedTo_ : A → A → Set (a ⊔ ℓ) where
  singleStep : ∀ x → x IsRelatedTo x
  multiStep  : ∀ {x y} (x∼y : x ∼ y) → x IsRelatedTo y

∼-go : Trans _∼_ _IsRelatedTo_ _IsRelatedTo_
∼-go x∼y (singleStep y) = multiStep x∼y
∼-go x∼y (multiStep y∼z) = multiStep (trans x∼y y∼z)

stop : Reflexive _IsRelatedTo_
stop = singleStep _

------------------------------------------------------------------------
-- Types that are used to ensure that the final relation proved by the
-- chain of reasoning can be converted into the required relation.

data IsMultiStep {x y} : x IsRelatedTo y → Set (a ⊔ ℓ) where
  isMultiStep : ∀ x∼y → IsMultiStep (multiStep x∼y)

IsMultiStep? : ∀ {x y} (x∼y : x IsRelatedTo y) → Dec (IsMultiStep x∼y)
IsMultiStep? (multiStep x<y) = yes (isMultiStep x<y)
IsMultiStep? (singleStep _)  = no λ()

extractMultiStep : ∀ {x y} {x∼y : x IsRelatedTo y} → IsMultiStep x∼y → x ∼ y
extractMultiStep (isMultiStep x≈y) = x≈y

multiStepSubRelation : SubRelation _IsRelatedTo_ _ _
multiStepSubRelation = record
  { IsS = IsMultiStep
  ; IsS? = IsMultiStep?
  ; extract = extractMultiStep
  }

------------------------------------------------------------------------
-- Reasoning combinators

open begin-subrelation-syntax _IsRelatedTo_ multiStepSubRelation public
open ≡-noncomputing-syntax _IsRelatedTo_ public
open ∼-syntax _IsRelatedTo_ _IsRelatedTo_ ∼-go public
open end-syntax _IsRelatedTo_ stop public


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.6

infix  3 _∎⟨_⟩

_∎⟨_⟩ : ∀ x → x ∼ x → x IsRelatedTo x
_ ∎⟨ x∼x ⟩ = multiStep x∼x
{-# WARNING_ON_USAGE _∎⟨_⟩
"Warning: _∎⟨_⟩ was deprecated in v1.6.
Please use _∎ instead if used in a chain, otherwise simply provide
the proof of reflexivity directly without using these combinators."
#-}
