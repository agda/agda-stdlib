------------------------------------------------------------------------
-- The Agda standard library
--
-- The basic code for equational reasoning with three relations:
-- equality and apartness
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)
open import Function.Base using (case_of_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Symmetric; Trans)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Reasoning.Syntax


module Relation.Binary.Reasoning.Base.Apartness {a ℓ₁ ℓ₂} {A : Set a}
  {_≈_ : Rel A ℓ₁} {_#_ : Rel A ℓ₂}
  (≈-equiv : IsEquivalence _≈_)
  (#-sym   : Symmetric _#_)
  (#-≈-trans : Trans _#_ _≈_ _#_) (≈-#-trans : Trans _≈_ _#_ _#_)
  where

module Eq = IsEquivalence ≈-equiv

------------------------------------------------------------------------
-- A datatype to hide the current relation type

infix 4 _IsRelatedTo_

data _IsRelatedTo_ (x y : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  nothing   :                 x IsRelatedTo y
  apartness : (x#y : x # y) → x IsRelatedTo y
  equals    : (x≈y : x ≈ y) → x IsRelatedTo y

≡-go : Trans _≡_ _IsRelatedTo_ _IsRelatedTo_
≡-go x≡y nothing = nothing
≡-go x≡y (apartness y#z) = apartness (case x≡y of λ where ≡.refl → y#z)
≡-go x≡y (equals y≈z) = equals (case x≡y of λ where ≡.refl → y≈z)

≈-go  : Trans _≈_ _IsRelatedTo_ _IsRelatedTo_
≈-go x≈y nothing         = nothing
≈-go x≈y (apartness y#z) = apartness (≈-#-trans x≈y y#z)
≈-go x≈y (equals    y≈z) = equals    (Eq.trans   x≈y y≈z)

#-go : Trans _#_ _IsRelatedTo_ _IsRelatedTo_
#-go x#y nothing         = nothing
#-go x#y (apartness y#z) = nothing
#-go x#y (equals    y≈z) = apartness (#-≈-trans x#y y≈z)

stop : Reflexive _IsRelatedTo_
stop = equals Eq.refl

------------------------------------------------------------------------
-- Apartness subrelation

data IsApartness {x y} : x IsRelatedTo y → Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  isApartness : ∀ x#y → IsApartness (apartness x#y)

IsApartness? : ∀ {x y} (x#y : x IsRelatedTo y) → Dec (IsApartness x#y)
IsApartness? nothing         = no λ()
IsApartness? (apartness x#y) = yes (isApartness x#y)
IsApartness? (equals x≈y)    = no (λ ())

extractApartness : ∀ {x y} {x#y : x IsRelatedTo y} → IsApartness x#y → x # y
extractApartness (isApartness x#y) = x#y

apartnessRelation : SubRelation _IsRelatedTo_ _ _
apartnessRelation = record
  { IsS = IsApartness
  ; IsS? = IsApartness?
  ; extract = extractApartness
  }

------------------------------------------------------------------------
-- Equality subrelation

data IsEquality {x y} : x IsRelatedTo y → Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  isEquality : ∀ x≈y → IsEquality (equals x≈y)

IsEquality? : ∀ {x y} (x≲y : x IsRelatedTo y) → Dec (IsEquality x≲y)
IsEquality? nothing       = no λ()
IsEquality? (apartness _) = no λ()
IsEquality? (equals  x≈y) = yes (isEquality x≈y)

extractEquality : ∀ {x y} {x≲y : x IsRelatedTo y} → IsEquality x≲y → x ≈ y
extractEquality (isEquality x≈y) = x≈y

eqRelation : SubRelation _IsRelatedTo_ _ _
eqRelation = record
  { IsS = IsEquality
  ; IsS? = IsEquality?
  ; extract = extractEquality
  }

------------------------------------------------------------------------
-- Reasoning combinators

open begin-apartness-syntax _IsRelatedTo_ apartnessRelation public
open begin-equality-syntax _IsRelatedTo_ eqRelation public
open ≡-syntax _IsRelatedTo_ ≡-go public
open #-syntax _IsRelatedTo_ _IsRelatedTo_ #-go #-sym public
open ≈-syntax _IsRelatedTo_ _IsRelatedTo_ ≈-go Eq.sym public
open end-syntax _IsRelatedTo_ stop public
