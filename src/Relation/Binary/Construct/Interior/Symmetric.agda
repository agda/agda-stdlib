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
    R : Rel A r
    S : Rel A s
    T : Rel A t

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

trans′ : Trans R S T → Trans S R T →
  Trans (SymInterior R) (SymInterior S) (SymInterior T)
trans′ trans-rs trans-sr (r , r′) (s , s′) = trans-rs r s , trans-sr s′ r′

transitive : Transitive R → Transitive (SymInterior R)
transitive {R = R} tr = trans′ {R = R} tr tr

-- The symmetric interior of a strict relation is empty.
Empty-SymInterior : Asymmetric R → Empty (SymInterior R)
Empty-SymInterior asym (r , r′) = asym r r′

-- A reflexive transitive relation _≤_ gives rise to a poset in which the
-- equivalence relation is SymInterior _≤_.
record IsProset {a ℓ} {A : Set a} (_≤_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  field
    refl : Reflexive _≤_
    trans : Transitive _≤_

record Proset c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≤_
  field
    Carrier : Set c
    _≤_ : Rel Carrier ℓ
    isProset : IsProset _≤_

IsProset⇒IsPartialOrder : ∀ {a ℓ} {A : Set a} {≤ : Rel A ℓ} →
  IsProset ≤ → IsPartialOrder (SymInterior ≤) ≤
IsProset⇒IsPartialOrder {≤ = ≤} isProset = record
  { isPreorder = record
    { isEquivalence = record
      { refl = reflexive refl
      ; sym = symmetric
      ; trans = transitive trans
      }
    ; reflexive = lhs≤rhs
    ; trans = trans
    }
  ; antisym = _,_
  } where open IsProset isProset

Proset⇒Poset : Proset c ℓ → Poset c ℓ ℓ
Proset⇒Poset record { isProset = isProset } =
  record { isPartialOrder = IsProset⇒IsPartialOrder isProset }
