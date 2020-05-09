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
  {_≈_ : Rel A ℓ₁} {_≤_ : Rel A ℓ₂} {_<_ : Rel A ℓ₃}
  (isPreorder : IsPreorder _≈_ _≤_)
  (<-trans : Transitive _<_) (<-resp-≈ : _<_ Respects₂ _≈_) (<⇒≤ : _<_ ⇒ _≤_)
  (<-≤-trans : Trans _<_ _≤_ _<_) (≤-<-trans : Trans _≤_ _<_ _<_)
  where

open import Data.Product using (proj₁; proj₂)
open import Function using (case_of_; id)
open import Level using (Level; _⊔_; Lift; lift)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)

open IsPreorder isPreorder
  renaming
  ( reflexive to ≤-reflexive
  ; trans     to ≤-trans
  ; ∼-resp-≈  to ≤-resp-≈
  )

------------------------------------------------------------------------
-- A datatype to abstract over the current relation

infix 4 _IsRelatedTo_

data _IsRelatedTo_ (x y : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  strict    : (x<y : x < y) → x IsRelatedTo y
  nonstrict : (x≤y : x ≤ y) → x IsRelatedTo y
  equals    : (x≈y : x ≈ y) → x IsRelatedTo y

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

data IsEquality {x y} : x IsRelatedTo y → Set (a ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  isEquality : ∀ x≈y → IsEquality (equals x≈y)

IsEquality? : ∀ {x y} (x≲y : x IsRelatedTo y) → Dec (IsEquality x≲y)
IsEquality? (strict    _) = no λ()
IsEquality? (nonstrict _) = no λ()
IsEquality? (equals x≈y)  = yes (isEquality x≈y)

extractEquality : ∀ {x y} {x≲y : x IsRelatedTo y} → IsEquality x≲y → x ≈ y
extractEquality (isEquality x≈y) = x≈y

------------------------------------------------------------------------
-- Reasoning combinators

-- See `Relation.Binary.Reasoning.Base.Partial` for the design decisions
-- behind these combinators.

infix  1 begin_ begin-strict_ begin-equality_
infixr 2 step-< step-≤ step-≈ step-≈˘ step-≡ step-≡˘ _≡⟨⟩_
infix  3 _∎

-- Beginnings of various types of proofs

begin_ : ∀ {x y} → x IsRelatedTo y → x ≤ y
begin (strict    x<y) = <⇒≤ x<y
begin (nonstrict x≤y) = x≤y
begin (equals    x≈y) = ≤-reflexive x≈y

begin-strict_ : ∀ {x y} (r : x IsRelatedTo y) → {s : True (IsStrict? r)} → x < y
begin-strict_ r {s} = extractStrict (toWitness s)

begin-equality_ : ∀ {x y} (r : x IsRelatedTo y) → {s : True (IsEquality? r)} → x ≈ y
begin-equality_ r {s} = extractEquality (toWitness s)

-- Step with the strict relation

step-< : ∀ (x : A) {y z} → y IsRelatedTo z → x < y → x IsRelatedTo z
step-< x (strict    y<z) x<y = strict (<-trans x<y y<z)
step-< x (nonstrict y≤z) x<y = strict (<-≤-trans x<y y≤z)
step-< x (equals    y≈z) x<y = strict (proj₁ <-resp-≈ y≈z x<y)

-- Step with the non-strict relation

step-≤ : ∀ (x : A) {y z} → y IsRelatedTo z → x ≤ y → x IsRelatedTo z
step-≤ x (strict    y<z) x≤y = strict    (≤-<-trans x≤y y<z)
step-≤ x (nonstrict y≤z) x≤y = nonstrict (≤-trans x≤y y≤z)
step-≤ x (equals    y≈z) x≤y = nonstrict (proj₁ ≤-resp-≈ y≈z x≤y)

-- Step with the setoid equality

step-≈  : ∀ (x : A) {y z} → y IsRelatedTo z → x ≈ y → x IsRelatedTo z
step-≈ x (strict    y<z) x≈y = strict    (proj₂ <-resp-≈ (Eq.sym x≈y) y<z)
step-≈ x (nonstrict y≤z) x≈y = nonstrict (proj₂ ≤-resp-≈ (Eq.sym x≈y) y≤z)
step-≈ x (equals    y≈z) x≈y = equals    (Eq.trans x≈y y≈z)

-- Flipped step with the setoid equality

step-≈˘ : ∀ x {y z} → y IsRelatedTo z → y ≈ x → x IsRelatedTo z
step-≈˘ x y∼z x≈y = step-≈ x y∼z (Eq.sym x≈y)

-- Step with non-trivial propositional equality

step-≡ : ∀ (x : A) {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
step-≡ x (strict    y<z) x≡y  = strict    (case x≡y of λ where refl → y<z)
step-≡ x (nonstrict y≤z) x≡y  = nonstrict (case x≡y of λ where refl → y≤z)
step-≡ x (equals    y≈z) x≡y  = equals    (case x≡y of λ where refl → y≈z)

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

syntax step-<  x y∼z x<y = x <⟨  x<y ⟩ y∼z
syntax step-≤  x y∼z x≤y = x ≤⟨  x≤y ⟩ y∼z
syntax step-≈  x y∼z x≈y = x ≈⟨  x≈y ⟩ y∼z
syntax step-≈˘ x y∼z y≈x = x ≈˘⟨ y≈x ⟩ y∼z
syntax step-≡  x y∼z x≡y = x ≡⟨  x≡y ⟩ y∼z
syntax step-≡˘ x y∼z y≡x = x ≡˘⟨ y≡x ⟩ y∼z
