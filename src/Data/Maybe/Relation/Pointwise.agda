------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of relations to maybes
------------------------------------------------------------------------

module Data.Maybe.Relation.Pointwise where

open import Level
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Binary
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec

------------------------------------------------------------------------
-- Definition

data Pointwise {a r} {A : Set a} (R : Rel A r) : Rel (Maybe A) r where
  just    : ∀ {x y} → R x y → Pointwise R (just x) (just y)
  nothing : Pointwise R nothing nothing

------------------------------------------------------------------------
-- Properties

module _ {a r} {A : Set a} {R : Rel A r} where

  drop-just : ∀ {x y} → Pointwise R (just x) (just y) → R x y
  drop-just (just p) = p

  just-equivalence : ∀ {x y} → R x y ⇔ Pointwise R (just x) (just y)
  just-equivalence = equivalence just drop-just

  refl : Reflexive R → Reflexive (Pointwise R)
  refl R-refl {just _}  = just R-refl
  refl R-refl {nothing} = nothing

  sym : Symmetric R → Symmetric (Pointwise R)
  sym R-sym (just p) = just (R-sym p)
  sym R-sym nothing  = nothing

  trans : Transitive R → Transitive (Pointwise R)
  trans R-trans (just p) (just q) = just (R-trans p q)
  trans R-trans nothing  nothing  = nothing

  dec : Decidable R → Decidable (Pointwise R)
  dec R-dec (just x) (just y) = Dec.map just-equivalence (R-dec x y)
  dec R-dec (just x) nothing  = no (λ ())
  dec R-dec nothing  (just y) = no (λ ())
  dec R-dec nothing  nothing  = yes nothing

  isEquivalence : IsEquivalence R → IsEquivalence (Pointwise R)
  isEquivalence R-isEquivalence = record
    { refl  = refl R.refl
    ; sym   = sym R.sym
    ; trans = trans R.trans
    } where module R = IsEquivalence R-isEquivalence

  isDecEquivalence : IsDecEquivalence R → IsDecEquivalence (Pointwise R)
  isDecEquivalence R-isDecEquivalence = record
    { isEquivalence = isEquivalence R.isEquivalence
    ; _≟_           = dec R._≟_
    } where module R = IsDecEquivalence R-isDecEquivalence

setoid : ∀ {c ℓ} → Setoid c ℓ → Setoid c ℓ
setoid S = record
  { isEquivalence = isEquivalence S.isEquivalence
  } where module S = Setoid S

decSetoid : ∀ {c ℓ} → DecSetoid c ℓ → DecSetoid c ℓ
decSetoid S = record
  { isDecEquivalence = isDecEquivalence S.isDecEquivalence
  } where module S = DecSetoid S
