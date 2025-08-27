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

-- This type allows us to track whether reasoning steps
-- include _∼_ or not.

infix  4 _IsRelatedTo_

data _IsRelatedTo_ : A → A → Set (a ⊔ ℓ) where
  reflexive : ∀ {x y} → x ≡ y → x IsRelatedTo y
  relTo     : ∀ {x y} (x∼y : x ∼ y) → x IsRelatedTo y

≡-go : Trans _≡_ _IsRelatedTo_ _IsRelatedTo_
≡-go x≡y (reflexive y≡z) = reflexive (case x≡y of λ where ≡.refl → y≡z)
≡-go x≡y (relTo y∼z)     = relTo (case x≡y of λ where ≡.refl → y∼z)

∼-go : Trans _∼_ _IsRelatedTo_ _IsRelatedTo_
∼-go x∼y (reflexive y≡z) = relTo (case y≡z of λ where ≡.refl → x∼y)
∼-go x∼y (relTo y∼z)     = relTo (trans x∼y y∼z)

stop : Reflexive _IsRelatedTo_
stop = reflexive ≡.refl

------------------------------------------------------------------------
-- Types that are used to ensure that the final relation proved by the
-- chain of reasoning can be converted into the required relation.

data IsRelTo {x y} : x IsRelatedTo y → Set (a ⊔ ℓ) where
  isRelTo : ∀ x∼y → IsRelTo (relTo x∼y)

IsRelTo? : ∀ {x y} (x∼y : x IsRelatedTo y) → Dec (IsRelTo x∼y)
IsRelTo? (relTo x∼y)   = yes (isRelTo x∼y)
IsRelTo? (reflexive _) = no λ()

extractRelTo : ∀ {x y} {x∼y : x IsRelatedTo y} → IsRelTo x∼y → x ∼ y
extractRelTo (isRelTo x∼y) = x∼y

relToSubRelation : SubRelation _IsRelatedTo_ _ _
relToSubRelation = record
  { IsS = IsRelTo
  ; IsS? = IsRelTo?
  ; extract = extractRelTo
  }

------------------------------------------------------------------------
-- Reasoning combinators

open begin-subrelation-syntax _IsRelatedTo_ relToSubRelation public
open ≡-syntax _IsRelatedTo_ ≡-go public
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
_ ∎⟨ x∼x ⟩ = relTo x∼x
{-# WARNING_ON_USAGE _∎⟨_⟩
"Warning: _∎⟨_⟩ was deprecated in v1.6.
Please use _∎ instead if used in a chain, otherwise simply provide
the proof of reflexivity directly without using these combinators."
#-}
