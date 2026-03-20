------------------------------------------------------------------------
-- The Agda standard library
--
-- The basic code for equational reasoning with two relations:
-- equality and some other ordering.
------------------------------------------------------------------------
--
-- See `Data.Nat.Properties` or `Relation.Binary.Reasoning.PartialOrder`
-- for examples of how to instantiate this module.

{-# OPTIONS --without-K --safe #-}

open import Level using (_⊔_)
open import Function.Base using (case_of_)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Definitions using (Reflexive; Trans)
open import Relation.Binary.Structures using (IsPreorder)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Reasoning.Syntax


module Relation.Binary.Reasoning.Base.Double {a ℓ₁ ℓ₂} {A : Set a}
  {_≈_ : Rel A ℓ₁} {_≲_ : Rel A ℓ₂} (isPreorder : IsPreorder _≈_ _≲_)
  where

open IsPreorder isPreorder

------------------------------------------------------------------------
-- A datatype to hide the current relation type

infix 4 _IsRelatedTo_

data _IsRelatedTo_ (x y : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  nonstrict : (x≲y : x ≲ y) → x IsRelatedTo y
  equals    : (x≈y : x ≈ y) → x IsRelatedTo y

start : _IsRelatedTo_ ⇒ _≲_
start (equals x≈y) = reflexive x≈y
start (nonstrict x≲y) = x≲y

≡-go : Trans _≡_ _IsRelatedTo_ _IsRelatedTo_
≡-go x≡y (equals y≈z) = equals (case x≡y of λ where ≡.refl → y≈z)
≡-go x≡y (nonstrict y≤z) = nonstrict (case x≡y of λ where ≡.refl → y≤z)

≲-go : Trans _≲_ _IsRelatedTo_ _IsRelatedTo_
≲-go x≲y (equals y≈z) = nonstrict (∼-respʳ-≈ y≈z x≲y)
≲-go x≲y (nonstrict y≲z) = nonstrict (trans x≲y y≲z)

≈-go : Trans _≈_ _IsRelatedTo_ _IsRelatedTo_
≈-go x≈y (equals y≈z) = equals (Eq.trans x≈y y≈z)
≈-go x≈y (nonstrict y≲z) = nonstrict (∼-respˡ-≈ (Eq.sym x≈y) y≲z)

stop : Reflexive _IsRelatedTo_
stop = equals Eq.refl

------------------------------------------------------------------------
-- A record that is used to ensure that the final relation proved by the
-- chain of reasoning can be converted into the required relation.

data IsEquality {x y} : x IsRelatedTo y → Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  isEquality : ∀ x≈y → IsEquality (equals x≈y)

IsEquality? : ∀ {x y} (x≲y : x IsRelatedTo y) → Dec (IsEquality x≲y)
IsEquality? (nonstrict _) = no λ()
IsEquality? (equals x≈y)  = yes (isEquality x≈y)

extractEquality : ∀ {x y} {x≲y : x IsRelatedTo y} → IsEquality x≲y → x ≈ y
extractEquality (isEquality x≈y) = x≈y

equalitySubRelation : SubRelation  _IsRelatedTo_ _ _
equalitySubRelation = record
  { IsS = IsEquality
  ; IsS? = IsEquality?
  ; extract = extractEquality
  }

------------------------------------------------------------------------
-- Reasoning combinators

open begin-syntax  _IsRelatedTo_ start public
open begin-equality-syntax  _IsRelatedTo_ equalitySubRelation public
open ≡-syntax _IsRelatedTo_ ≡-go public
open ≈-syntax _IsRelatedTo_ _IsRelatedTo_ ≈-go Eq.sym public
open ≲-syntax _IsRelatedTo_ _IsRelatedTo_ ≲-go public
open end-syntax _IsRelatedTo_ stop public


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

open ∼-syntax _IsRelatedTo_ _IsRelatedTo_ ≲-go public
{-# WARNING_ON_USAGE step-∼
"Warning: step-∼ and _∼⟨_⟩_ syntax was deprecated in v2.0.
Please use step-≲ and _≲⟨_⟩_ instead. "
#-}
