------------------------------------------------------------------------
-- The Agda standard library
--
-- Symmetric interior of a binary relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.Interior.Symmetric where

open import Function.Base using (flip)
open import Level
open import Relation.Binary

private
  variable
    a b c ℓ r s t : Level
    A : Set a
    R S T : Rel A r

------------------------------------------------------------------------
-- Definition

record SymInterior (R : Rel A ℓ) (x y : A) : Set ℓ where
  constructor _,_
  field
    lhs≤rhs : R x y
    rhs≤lhs : R y x

open SymInterior public

------------------------------------------------------------------------
-- Properties

-- The symmetric interior is symmetric.
symmetric : Symmetric (SymInterior R)
symmetric (r , r′) = r′ , r

-- The symmetric interior of R is greater than (or equal to) any other symmetric
-- relation contained by R.
unfold : Symmetric S → S ⇒ R → S ⇒ SymInterior R
unfold sym f s = f s , f (sym s)

-- SymInterior preserves various properties.
reflexive : Reflexive R → Reflexive (SymInterior R)
reflexive refl = refl , refl

trans : Trans R S T → Trans S R T →
  Trans (SymInterior R) (SymInterior S) (SymInterior T)
trans trans-rs trans-sr (r , r′) (s , s′) = trans-rs r s , trans-sr s′ r′

transitive : Transitive R → Transitive (SymInterior R)
transitive tr = trans tr tr

-- The symmetric interior of a strict relation is empty.
asymmetric⇒empty : Asymmetric R → Empty (SymInterior R)
asymmetric⇒empty asym (r , r′) = asym r r′

-- A reflexive transitive relation _≤_ gives rise to a poset in which the
-- equivalence relation is SymInterior _≤_.

isEquivalence : Reflexive R → Transitive R → IsEquivalence (SymInterior R)
isEquivalence refl trans = record
  { refl = reflexive refl
  ; sym = symmetric
  ; trans = transitive trans
  }

isPartialOrder : Reflexive R → Transitive R → IsPartialOrder (SymInterior R) R
isPartialOrder refl trans = record
  { isPreorder = record
    { isEquivalence = isEquivalence refl trans
    ; reflexive = lhs≤rhs
    ; trans = trans
    }
  ; antisym = _,_
  }

poset : ∀ {a} {A : Set a} {R : Rel A ℓ} → Reflexive R → Transitive R → Poset a ℓ ℓ
poset {R = R} refl trans = record
  { _≤_ = R
  ; isPartialOrder = isPartialOrder refl trans
  }
