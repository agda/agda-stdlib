------------------------------------------------------------------------
-- The Agda standard library
--
-- The basic code for equational reasoning with three relations:
-- equality and apartness
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary

module Relation.Binary.Reasoning.Base.Apartness {a ℓ₁ ℓ₂} {A : Set a}
  {_≈_ : Rel A ℓ₁} {_#_ : Rel A ℓ₂}
  (≈-equiv : IsEquivalence _≈_)
  (#-trans : Transitive _#_) (#-sym   : Symmetric _#_)
  (#-≈-trans : Trans _#_ _≈_ _#_) (≈-#-trans : Trans _≈_ _#_ _#_)
  where

open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)

open IsEquivalence ≈-equiv
  renaming
  ( refl  to ≈-refl
  ; sym   to ≈-sym
  ; trans to ≈-trans
  )

infix 4 _IsRelatedTo_

data _IsRelatedTo_ (x y : A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  nothing   :                 x IsRelatedTo y
  apartness : (x#y : x # y) → x IsRelatedTo y
  equals    : (x≈y : x ≈ y) → x IsRelatedTo y

data IsApartness {x y} : x IsRelatedTo y → Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  isApartness : ∀ x#y → IsApartness (apartness x#y)

IsApartness? : ∀ {x y} (x#y : x IsRelatedTo y) → Dec (IsApartness x#y)
IsApartness? nothing         = no λ()
IsApartness? (apartness x#y) = yes (isApartness x#y)
IsApartness? (equals x≈y)    = no (λ ())

extractApartness : ∀ {x y} {x#y : x IsRelatedTo y} → IsApartness x#y → x # y
extractApartness (isApartness x#y) = x#y

data IsEquality {x y} : x IsRelatedTo y → Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  isEquality : ∀ x≈y → IsEquality (equals x≈y)

IsEquality? : ∀ {x y} (x≲y : x IsRelatedTo y) → Dec (IsEquality x≲y)
IsEquality? nothing       = no λ()
IsEquality? (apartness _) = no λ()
IsEquality? (equals  x≈y) = yes (isEquality x≈y)

extractEquality : ∀ {x y} {x≲y : x IsRelatedTo y} → IsEquality x≲y → x ≈ y
extractEquality (isEquality x≈y) = x≈y

infix  1 begin-apartness_ begin-equality_
infixr 2 step-≈ step-≈˘ step-≡ step-≡˘ step-# step-#˘ _≡⟨⟩_
infix  3 _∎

begin-apartness_ : ∀ {x y} (r : x IsRelatedTo y) → {s : True (IsApartness? r)} → x # y
begin-apartness_ _ {s} = extractApartness (toWitness s)

begin-equality_ : ∀ {x y} (r : x IsRelatedTo y) → {s : True (IsEquality? r)} → x ≈ y
begin-equality_ _ {s} = extractEquality (toWitness s)

step-# : ∀ (x : A) {y z} → y IsRelatedTo z → x # y → x IsRelatedTo z
step-# x nothing  _          = nothing
step-# x (apartness y#z) x#y = nothing
step-# x (equals    y≈z) x#y = apartness (#-≈-trans x#y y≈z)

step-#˘ : ∀ (x : A) {y z} → y IsRelatedTo z → y # x → x IsRelatedTo z
step-#˘ x y-z y#x = step-# x y-z (#-sym y#x)

step-≈  : ∀ (x : A) {y z} → y IsRelatedTo z → x ≈ y → x IsRelatedTo z
step-≈ x nothing         x≈y = nothing
step-≈ x (apartness y#z) x≈y = apartness (≈-#-trans x≈y y#z)
step-≈ x (equals    y≈z) x≈y = equals    (≈-trans   x≈y y≈z)

step-≈˘ : ∀ x {y z} → y IsRelatedTo z → y ≈ x → x IsRelatedTo z
step-≈˘ x y∼z x≈y = step-≈ x y∼z (≈-sym x≈y)

step-≡ : ∀ (x : A) {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
step-≡ x nothing _            = nothing
step-≡ x (apartness x#y) refl = apartness x#y
step-≡ x (equals    x≈y) refl = equals    x≈y

step-≡˘ : ∀ x {y z} → y IsRelatedTo z → y ≡ x → x IsRelatedTo z
step-≡˘ x y∼z x≡y = step-≡ x y∼z (sym x≡y)

_≡⟨⟩_ : ∀ (x : A) {y} → x IsRelatedTo y → x IsRelatedTo y
x ≡⟨⟩ x-y = x-y

_∎ : ∀ x → x IsRelatedTo x
x ∎ = equals ≈-refl

syntax step-#  x y∼z x#y = x #⟨  x#y ⟩ y∼z
syntax step-#˘ x y∼z x#y = x #˘⟨ x#y ⟩ y∼z
syntax step-≈  x y∼z x≈y = x ≈⟨  x≈y ⟩ y∼z
syntax step-≈˘ x y∼z y≈x = x ≈˘⟨ y≈x ⟩ y∼z
syntax step-≡  x y∼z x≡y = x ≡⟨  x≡y ⟩ y∼z
syntax step-≡˘ x y∼z y≡x = x ≡˘⟨ y≡x ⟩ y∼z
