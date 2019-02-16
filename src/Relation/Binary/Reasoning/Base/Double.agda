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

open import Relation.Binary

module Relation.Binary.Reasoning.Base.Double {a ℓ₁ ℓ₂} {A : Set a}
  {_≈_ : Rel A ℓ₁} {_∼_ : Rel A ℓ₂} (isPreorder : IsPreorder _≈_ _∼_)
  where

open import Data.Product using (proj₁; proj₂)
open import Level using (Level; _⊔_; Lift; lift)
open import Function using (case_of_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)

open IsPreorder isPreorder

------------------------------------------------------------------------
-- A datatype to hide the current relation type

data _IsRelatedTo_ (x y : A) : Set (ℓ₁ ⊔ ℓ₂) where
  nonstrict : (x∼y : x ∼ y) → x IsRelatedTo y
  equals    : (x≈y : x ≈ y) → x IsRelatedTo y

levelOf : ∀ {x y} → x IsRelatedTo y → Level
levelOf (nonstrict x∼y) = ℓ₂
levelOf (equals    x≈y) = ℓ₁

relOf : ∀ {x y} (r : x IsRelatedTo y) → Rel A (levelOf r)
relOf (nonstrict x∼y) = _∼_
relOf (equals    x≈y) = _≈_

------------------------------------------------------------------------
-- A record that is used to ensure that the final relation proved by the
-- chain of reasoning can be converted into the required relation.

data IsEquality {x y} : x IsRelatedTo y → Set ℓ₁ where
  isEquality : ∀ x≈y → IsEquality (equals x≈y)

IsEquality? : ∀ {x y} (x≲y : x IsRelatedTo y) → Dec (IsEquality x≲y)
IsEquality? (nonstrict _) = no λ()
IsEquality? (equals x≈y)  = yes (isEquality x≈y)

extractEquality : ∀ {x y} {x≲y : x IsRelatedTo y} → IsEquality x≲y → x ≈ y
extractEquality (isEquality x≈y) = x≈y

------------------------------------------------------------------------
-- Reasoning combinators

infix -1 begin_ begin-equality_
infixr 0 _∼⟨_⟩_ _≈⟨_⟩_ _≈˘⟨_⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_ _≡⟨⟩_
infix  1 _∎

begin_ : ∀ {x y} (r : x IsRelatedTo y) → x ∼ y
begin (nonstrict x∼y) = x∼y
begin (equals    x≈y) = reflexive x≈y

begin-equality_ : ∀ {x y} (r : x IsRelatedTo y) → {s : True (IsEquality? r)} → x ≈ y
begin-equality_ r {s} = extractEquality (toWitness s)

_∼⟨_⟩_ : ∀ (x : A) {y z} → x ∼ y → y IsRelatedTo z → x IsRelatedTo z
x ∼⟨ x∼y ⟩ nonstrict y∼z = nonstrict (trans x∼y y∼z)
x ∼⟨ x∼y ⟩ equals    y≈z = nonstrict (proj₁ ∼-resp-≈ y≈z x∼y)

_≈⟨_⟩_ : ∀ (x : A) {y z} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
x ≈⟨ x≈y ⟩ nonstrict y∼z = nonstrict (proj₂ ∼-resp-≈ (Eq.sym x≈y) y∼z)
x ≈⟨ x≈y ⟩ equals    y≈z = equals    (Eq.trans x≈y y≈z)

_≈˘⟨_⟩_ : ∀ x {y z} → y ≈ x → y IsRelatedTo z → x IsRelatedTo z
x ≈˘⟨ x≈y ⟩ y∼z = x ≈⟨ Eq.sym x≈y ⟩ y∼z

_≡⟨_⟩_ : ∀ (x : A) {y z} → x ≡ y → y IsRelatedTo z → x IsRelatedTo z
x ≡⟨ x≡y ⟩ nonstrict y∼z = nonstrict (case x≡y of λ where refl → y∼z)
x ≡⟨ x≡y ⟩ equals    y≈z = equals    (case x≡y of λ where refl → y≈z)

_≡˘⟨_⟩_ : ∀ x {y z} → y ≡ x → y IsRelatedTo z → x IsRelatedTo z
x ≡˘⟨ x≡y ⟩ y∼z = x ≡⟨ sym x≡y ⟩ y∼z

_≡⟨⟩_ : ∀ (x : A) {y} → x IsRelatedTo y → x IsRelatedTo y
x ≡⟨⟩ x≲y = x≲y

_∎ : ∀ x → x IsRelatedTo x
x ∎ = equals Eq.refl

------------------------------------------------------------------------
-- Some examples and tests

{-
private
  module Examples where
    postulate
      u v w y d e : A
      u≈v : u ≈ v
      v≡w : v ≡ w
      w∼y : w ∼ y
      z≡d : y ≡ d
      d≈e : d ≈ e

    u∼y : u ∼ y
    u∼y = begin
      u ≈⟨ u≈v ⟩
      v ≡⟨ v≡w ⟩
      w ∼⟨ w∼y ⟩
      y ∎

    u≈w : u ≈ w
    u≈w = begin-equality
      u ≈⟨ u≈v ⟩
      v ≡⟨ v≡w ⟩
      w ∎
-}
