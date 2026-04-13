------------------------------------------------------------------------
-- The Agda standard library
--
-- The basic code for equational reasoning with three relations:
-- equality, strict ordering and non-strict ordering.
------------------------------------------------------------------------
--
-- See `Data.Nat.Properties` or `Relation.Binary.Reasoning.PartialOrder`
-- for examples of how to instantiate this module.

{-# OPTIONS --without-K --safe #-}


open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Structures using (IsPreorder)
open import Relation.Binary.Definitions
  using (Transitive; _Respects₂_; Reflexive; Trans; Irreflexive; Asymmetric)

module Relation.Binary.Reasoning.Base.Triple {a ℓ₁ ℓ₂ ℓ₃} {A : Set a}
  {_≈_ : Rel A ℓ₁} {_≤_ : Rel A ℓ₂} {_<_ : Rel A ℓ₃}
  (isPreorder : IsPreorder _≈_ _≤_)
  (<-asym : Asymmetric _<_) (<-trans : Transitive _<_) (<-resp-≈ : _<_ Respects₂ _≈_)
  (<⇒≤ : _<_ ⇒ _≤_)
  (<-≤-trans : Trans _<_ _≤_ _<_) (≤-<-trans : Trans _≤_ _<_ _<_)
  where

open import Data.Product.Base using (proj₁; proj₂)
open import Level using (_⊔_)
open import Function.Base using (case_of_)
open import Relation.Nullary.Decidable.Core
  using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Reasoning.Syntax

open IsPreorder isPreorder

------------------------------------------------------------------------
-- A datatype to abstract over the current relation

infix 4 _IsRelatedTo_

data _IsRelatedTo_ (x y : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  strict    : (x<y : x < y) → x IsRelatedTo y
  nonstrict : (x≤y : x ≤ y) → x IsRelatedTo y
  equals    : (x≈y : x ≈ y) → x IsRelatedTo y

start : _IsRelatedTo_ ⇒ _≤_
start (equals x≈y) = reflexive x≈y
start (nonstrict x≤y) = x≤y
start (strict x<y) = <⇒≤ x<y

≡-go : Trans _≡_ _IsRelatedTo_ _IsRelatedTo_
≡-go x≡y (equals y≈z) = equals (case x≡y of λ where ≡.refl → y≈z)
≡-go x≡y (nonstrict y≤z) = nonstrict (case x≡y of λ where ≡.refl → y≤z)
≡-go x≡y (strict y<z) = strict (case x≡y of λ where ≡.refl → y<z)

≈-go : Trans _≈_ _IsRelatedTo_ _IsRelatedTo_
≈-go x≈y (equals y≈z) = equals (Eq.trans x≈y y≈z)
≈-go x≈y (nonstrict y≤z) = nonstrict (∼-respˡ-≈ (Eq.sym x≈y) y≤z)
≈-go x≈y (strict y<z) = strict (proj₂ <-resp-≈ (Eq.sym x≈y) y<z)

≤-go : Trans _≤_ _IsRelatedTo_ _IsRelatedTo_
≤-go x≤y (equals y≈z) = nonstrict (∼-respʳ-≈ y≈z x≤y)
≤-go x≤y (nonstrict y≤z) = nonstrict (trans x≤y y≤z)
≤-go x≤y (strict y<z) = strict (≤-<-trans x≤y y<z)

<-go : Trans _<_ _IsRelatedTo_ _IsRelatedTo_
<-go x<y (equals y≈z) = strict (proj₁ <-resp-≈ y≈z x<y)
<-go x<y (nonstrict y≤z) = strict (<-≤-trans x<y y≤z)
<-go x<y (strict y<z) = strict (<-trans x<y y<z)

stop : Reflexive _IsRelatedTo_
stop = equals Eq.refl


------------------------------------------------------------------------
-- Types that are used to ensure that the final relation proved by the
-- chain of reasoning can be converted into the required relation.

data IsStrict {x y} : x IsRelatedTo y → Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  isStrict : ∀ x<y → IsStrict (strict x<y)

IsStrict? : ∀ {x y} (x≲y : x IsRelatedTo y) → Dec (IsStrict x≲y)
IsStrict? (strict    x<y) = yes (isStrict x<y)
IsStrict? (nonstrict _)   = no λ()
IsStrict? (equals    _)   = no λ()

extractStrict : ∀ {x y} {x≲y : x IsRelatedTo y} → IsStrict x≲y → x < y
extractStrict (isStrict x<y) = x<y

strictRelation : SubRelation _IsRelatedTo_ _ _
strictRelation = record
  { IsS = IsStrict
  ; IsS? = IsStrict?
  ; extract = extractStrict
  }

------------------------------------------------------------------------
-- Equality sub-relation

data IsEquality {x y} : x IsRelatedTo y → Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  isEquality : ∀ x≈y → IsEquality (equals x≈y)

IsEquality? : ∀ {x y} (x≲y : x IsRelatedTo y) → Dec (IsEquality x≲y)
IsEquality? (strict    _) = no λ()
IsEquality? (nonstrict _) = no λ()
IsEquality? (equals x≈y)  = yes (isEquality x≈y)

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

open begin-syntax _IsRelatedTo_ start public
open begin-equality-syntax _IsRelatedTo_ eqRelation public
open begin-strict-syntax _IsRelatedTo_ strictRelation public
open begin-contradiction-syntax _IsRelatedTo_ strictRelation <-asym public
open ≡-syntax _IsRelatedTo_ ≡-go public
open ≈-syntax _IsRelatedTo_ _IsRelatedTo_ ≈-go Eq.sym public
open ≤-syntax _IsRelatedTo_ _IsRelatedTo_ ≤-go public
open <-syntax _IsRelatedTo_ _IsRelatedTo_ <-go public
open end-syntax _IsRelatedTo_ stop public
