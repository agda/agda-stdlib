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
open import Function.Base using (case_of_; id)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)

open IsPreorder isPreorder

------------------------------------------------------------------------
-- A datatype to hide the current relation type

infix 4 _IsRelatedTo_

data _IsRelatedTo_ (x y : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  nonstrict : (x∼y : x ∼ y) → x IsRelatedTo y
  equals    : (x≈y : x ≈ y) → x IsRelatedTo y

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

------------------------------------------------------------------------
-- Reasoning combinators

-- See `Relation.Binary.Reasoning.Base.Partial` for the design decisions
-- behind these combinators.

infix  1 begin_ begin-equality_
infixr 2 step-∼ step-≈ step-≈˘ step-≡ step-≡˘ _≡⟨⟩_
infix  3 _∎

-- Beginnings of various types of proofs

begin_ : ∀ {x y} (r : x IsRelatedTo y) → x ∼ y
begin (nonstrict x∼y) = x∼y
begin (equals    x≈y) = reflexive x≈y

begin-equality_ : ∀ {x y} (r : x IsRelatedTo y) → {s : True (IsEquality? r)} → x ≈ y
begin-equality_ r {s} = extractEquality (toWitness s)

-- Step with the main relation

step-∼ : ∀ (x : A) {y z} → y IsRelatedTo z → x ∼ y → x IsRelatedTo z
step-∼ x (nonstrict y∼z) x∼y = nonstrict (trans x∼y y∼z)
step-∼ x (equals    y≈z) x∼y = nonstrict (∼-respʳ-≈ y≈z x∼y)

-- Step with the setoid equality

step-≈ : ∀ (x : A) {y z} → y IsRelatedTo z → x ≈ y → x IsRelatedTo z
step-≈ x (nonstrict y∼z) x≈y = nonstrict (∼-respˡ-≈ (Eq.sym x≈y) y∼z)
step-≈ x (equals    y≈z) x≈y = equals    (Eq.trans x≈y y≈z)

-- Flipped step with the setoid equality

step-≈˘ : ∀ x {y z} → y IsRelatedTo z → y ≈ x → x IsRelatedTo z
step-≈˘ x y∼z x≈y = step-≈ x y∼z (Eq.sym x≈y)

-- Step with non-trivial propositional equality

step-≡ : ∀ (x : A) {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
step-≡ x (nonstrict y∼z) x≡y = nonstrict (case x≡y of λ where refl → y∼z)
step-≡ x (equals    y≈z) x≡y = equals    (case x≡y of λ where refl → y≈z)

-- Flipped step with non-trivial propositional equality

step-≡˘ : ∀ x {y z} → y IsRelatedTo z → y ≡ x → x IsRelatedTo z
step-≡˘ x y∼z x≡y = step-≡ x y∼z (sym x≡y)

-- Step with trivial propositional equality

_≡⟨⟩_ : ∀ (x : A) {y} → x IsRelatedTo y → x IsRelatedTo y
x ≡⟨⟩ x≲y = x≲y

-- Termination step

_∎ : ∀ x → x IsRelatedTo x
x ∎ = equals Eq.refl

-- Syntax declarations

syntax step-∼  x y∼z x∼y = x ∼⟨  x∼y ⟩ y∼z
syntax step-≈  x y∼z x≈y = x ≈⟨  x≈y ⟩ y∼z
syntax step-≈˘ x y∼z y≈x = x ≈˘⟨ y≈x ⟩ y∼z
syntax step-≡  x y∼z x≡y = x ≡⟨  x≡y ⟩ y∼z
syntax step-≡˘ x y∼z y≡x = x ≡˘⟨ y≡x ⟩ y∼z
