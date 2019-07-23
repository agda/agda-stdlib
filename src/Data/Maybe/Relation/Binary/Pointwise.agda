------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of relations to maybes
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Maybe.Relation.Binary.Pointwise where

open import Level
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec

------------------------------------------------------------------------
-- Definition

data Pointwise
       {a b ℓ} {A : Set a} {B : Set b}
       (R : REL A B ℓ) : REL (Maybe A) (Maybe B) (a ⊔ b ⊔ ℓ) where
  just    : ∀ {x y} → R x y → Pointwise R (just x) (just y)
  nothing : Pointwise R nothing nothing

------------------------------------------------------------------------
-- Properties

module _ {a b ℓ} {A : Set a} {B : Set b} {R : REL A B ℓ} where

  drop-just : ∀ {x y} → Pointwise R (just x) (just y) → R x y
  drop-just (just p) = p

  just-equivalence : ∀ {x y} → R x y ⇔ Pointwise R (just x) (just y)
  just-equivalence = equivalence just drop-just

------------------------------------------------------------------------
-- Relational properties

module _ {a r} {A : Set a} {R : Rel A r} where

  refl : Reflexive R → Reflexive (Pointwise R)
  refl R-refl {just _}  = just R-refl
  refl R-refl {nothing} = nothing

  reflexive : _≡_ ⇒ R → _≡_ ⇒ Pointwise R
  reflexive reflexive P.refl = refl (reflexive P.refl)

module _ {a b r₁ r₂} {A : Set a} {B : Set b}
         {R : REL A B r₁} {S : REL B A r₂} where

  sym : Sym R S → Sym (Pointwise R) (Pointwise S)
  sym R-sym (just p) = just (R-sym p)
  sym R-sym nothing  = nothing

module _ {a b c r₁ r₂ r₃} {A : Set a} {B : Set b} {C : Set c}
         {R : REL A B r₁} {S : REL B C r₂} {T : REL A C r₃} where

  trans : Trans R S T → Trans (Pointwise R) (Pointwise S) (Pointwise T)
  trans R-trans (just p) (just q) = just (R-trans p q)
  trans R-trans nothing  nothing  = nothing

module _ {a r} {A : Set a} {R : Rel A r} where

  dec : Decidable R → Decidable (Pointwise R)
  dec R-dec (just x) (just y) = Dec.map just-equivalence (R-dec x y)
  dec R-dec (just x) nothing  = no (λ ())
  dec R-dec nothing  (just y) = no (λ ())
  dec R-dec nothing  nothing  = yes nothing

  isPartialEquivalence : IsPartialEquivalence R → IsPartialEquivalence (Pointwise R)
  isPartialEquivalence R-isPartialEquivalence = record
    { sym   = sym R.sym
    ; trans = trans R.trans
    } where module R = IsPartialEquivalence R-isPartialEquivalence

  isEquivalence : IsEquivalence R → IsEquivalence (Pointwise R)
  isEquivalence R-isEquivalence = record
    { isPartialEquivalence = isPartialEquivalence R.isPartialEquivalence
    ; refl  = refl R.refl
    } where module R = IsEquivalence R-isEquivalence

  isDecEquivalence : IsDecEquivalence R → IsDecEquivalence (Pointwise R)
  isDecEquivalence R-isDecEquivalence = record
    { isEquivalence = isEquivalence R.isEquivalence
    ; _≟_           = dec R._≟_
    } where module R = IsDecEquivalence R-isDecEquivalence

module _ {c ℓ} where

  setoid : Setoid c ℓ → Setoid c (c ⊔ ℓ)
  setoid S = record
    { isEquivalence = isEquivalence S.isEquivalence
    } where module S = Setoid S

  decSetoid : DecSetoid c ℓ → DecSetoid c (c ⊔ ℓ)
  decSetoid S = record
    { isDecEquivalence = isDecEquivalence S.isDecEquivalence
    } where module S = DecSetoid S
