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

open import Relation.Binary

module Relation.Binary.Reasoning.Base.Triple {a ℓ₁ ℓ₂ ℓ₃} {A : Set a}
  {_≈_ : Rel A ℓ₁} (isEquivalence : IsEquivalence _≈_)
  {_≤_ : Rel A ℓ₂} (≤-trans : Transitive _≤_) (≤-resp-≈ : _≤_ Respects₂ _≈_) (≤-reflexive : _≈_ ⇒ _≤_)
  {_<_ : Rel A ℓ₃} (<-trans : Transitive _<_) (<-resp-≈ : _<_ Respects₂ _≈_) (<⇒≤ : _<_ ⇒ _≤_)
  (<-≤-trans : Trans _<_ _≤_ _<_)
  (≤-<-trans : Trans _≤_ _<_ _<_)
  where

open import Data.Product using (proj₁; proj₂)
open import Function using (case_of_; id)
open import Level using (Level; _⊔_; Lift; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)

open IsEquivalence isEquivalence
  renaming
  ( refl  to ≈-refl
  ; sym   to ≈-sym
  ; trans to ≈-trans
  )

------------------------------------------------------------------------
-- A datatype to hide the current relation type

data _IsRelatedTo_ (x y : A) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  strict    : (x<y : x < y) → x IsRelatedTo y
  nonstrict : (x≤y : x ≤ y) → x IsRelatedTo y
  equals    : (x≈y : x ≈ y) → x IsRelatedTo y

------------------------------------------------------------------------
-- Records that are used to ensure that the final relation proved by the
-- chain of reasoning can be converted into the required relation.

data IsStrict {x y} : x IsRelatedTo y → Set ℓ₃ where
  isStrict : ∀ x<y → IsStrict (strict x<y)

IsStrict? : ∀ {x y} (x≲y : x IsRelatedTo y) → Dec (IsStrict x≲y)
IsStrict? (strict    x<y) = yes (isStrict x<y)
IsStrict? (nonstrict _)   = no λ()
IsStrict? (equals    _)   = no λ()

extractStrict : ∀ {x y} {x≲y : x IsRelatedTo y} → IsStrict x≲y → x < y
extractStrict (isStrict x<y) = x<y

data IsEquality {x y} : x IsRelatedTo y → Set ℓ₁ where
  isEquality : ∀ x≈y → IsEquality (equals x≈y)

IsEquality? : ∀ {x y} (x≲y : x IsRelatedTo y) → Dec (IsEquality x≲y)
IsEquality? (strict    _) = no λ()
IsEquality? (nonstrict _) = no λ()
IsEquality? (equals x≈y)  = yes (isEquality x≈y)

extractEquality : ∀ {x y} {x≲y : x IsRelatedTo y} → IsEquality x≲y → x ≈ y
extractEquality (isEquality x≈y) = x≈y

------------------------------------------------------------------------
-- Reasoning combinators

infix -1 begin_ begin-strict_ begin-equality_
infixr 0 _<⟨_⟩_ _≤⟨_⟩_ _≈⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
infix  1 _∎

begin_ : ∀ {x y} (r : x IsRelatedTo y) → x ≤ y
begin (strict    x<y) = <⇒≤ x<y
begin (nonstrict x≤y) = x≤y
begin (equals    x≈y) = ≤-reflexive x≈y

begin-strict_ : ∀ {x y} (r : x IsRelatedTo y) → {s : True (IsStrict? r)} → x < y
begin-strict_ r {s} = extractStrict (toWitness s)

begin-equality_ : ∀ {x y} (r : x IsRelatedTo y) → {s : True (IsEquality? r)} → x ≈ y
begin-equality_ r {s} = extractEquality (toWitness s)

_<⟨_⟩_ : ∀ (x : A) {y z} → x < y → y IsRelatedTo z → x IsRelatedTo z
x <⟨ x<y ⟩ strict    y<z = strict (<-trans x<y y<z)
x <⟨ x<y ⟩ nonstrict y≤z = strict (<-≤-trans x<y y≤z)
x <⟨ x<y ⟩ equals    y≈z = strict (proj₁ <-resp-≈ y≈z x<y)

_≤⟨_⟩_ : ∀ (x : A) {y z} → x ≤ y → y IsRelatedTo z → x IsRelatedTo z
x ≤⟨ x≤y ⟩ strict    y<z = strict    (≤-<-trans x≤y y<z)
x ≤⟨ x≤y ⟩ nonstrict y≤z = nonstrict (≤-trans x≤y y≤z)
x ≤⟨ x≤y ⟩ equals    y≈z = nonstrict (proj₁ ≤-resp-≈ y≈z x≤y)

_≈⟨_⟩_ : ∀ (x : A) {y z} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
x ≈⟨ x≈y ⟩ strict    y<z = strict    (proj₂ <-resp-≈ (≈-sym x≈y) y<z)
x ≈⟨ x≈y ⟩ nonstrict y≤z = nonstrict (proj₂ ≤-resp-≈ (≈-sym x≈y) y≤z)
x ≈⟨ x≈y ⟩ equals    y≈z = equals    (≈-trans x≈y y≈z)

_≡⟨_⟩_ : ∀ (x : A) {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
x ≡⟨ x≡y ⟩ strict    y<z = strict    (case x≡y of λ where refl → y<z)
x ≡⟨ x≡y ⟩ nonstrict y≤z = nonstrict (case x≡y of λ where refl → y≤z)
x ≡⟨ x≡y ⟩ equals    y≈z = equals    (case x≡y of λ where refl → y≈z)

_≡⟨⟩_ : ∀ (x : A) {y} → x IsRelatedTo y → x IsRelatedTo y
x ≡⟨⟩ x≲y = x≲y

_∎ : ∀ x → x IsRelatedTo x
x ∎ = equals ≈-refl

------------------------------------------------------------------------
-- Some examples and tests

{-
private
  module Examples where
    postulate
      u v w x y z d e : A
      u≈v : u ≈ v
      v≡w : v ≡ w
      w<x : w < x
      x≤y : x ≤ y
      y<z : y < z
      z≡d : z ≡ d
      d≈e : d ≈ e

    u≤y : u ≤ y
    u≤y = begin
      u ≈⟨ u≈v ⟩
      v ≡⟨ v≡w ⟩
      w ≤⟨ <⇒≤ (<-≤-trans w<x x≤y) ⟩
      y ∎

    u≤c : u < e
    u≤c = begin-strict
      u ≈⟨ u≈v ⟩
      v ≡⟨ v≡w ⟩
      w <⟨ w<x ⟩
      x ≤⟨ x≤y ⟩
      y <⟨ y<z ⟩
      z ≡⟨ z≡d ⟩
      d ≈⟨ d≈e ⟩
      e ∎

    u≈w : u ≈ w
    u≈w = begin-equality
      u ≈⟨ u≈v ⟩
      v ≡⟨ v≡w ⟩
      w ∎
-}
