------------------------------------------------------------------------
-- The Agda standard library
--
-- Symmetric core of a binary relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.SymmetricCore where

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

record SymCore (R : Rel A ℓ) (x y : A) : Set ℓ where
  constructor _,_
  field
    holds : R x y
    sdolh : R y x
open SymCore public

------------------------------------------------------------------------
-- Properties

-- Symmetric cores are symmetric
symmetric : Symmetric (SymCore R)
symmetric (r , r′) = r′ , r

-- SymCore preserves various properties
reflexive : Reflexive R → Reflexive (SymCore R)
reflexive refl = refl , refl

transitive′ :
  Trans R S T → Trans S R T → Trans (SymCore R) (SymCore S) (SymCore T)
transitive′ trans trans′ (r , r′) (s , s′) = trans r s , trans′ s′ r′

transitive : Transitive R → Transitive (SymCore R)
transitive {R = R} tr = transitive′ {R = R} tr tr

-- The symmetric core of a strict relation is empty
Empty-SymCore : Asymmetric R → Empty (SymCore R)
Empty-SymCore asym (r , r′) = asym r r′

-- A reflexive transitive relation _≤_ gives rise to a poset in which the
-- equivalence relation is SymCore _≤_
record IsProset {a ℓ} {A : Set a} (≤ : Rel A ℓ) : Set (a ⊔ ℓ) where
  field
    refl : Reflexive ≤
    trans : Transitive ≤

record Proset c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≤_
  field
    Carrier : Set c
    _≤_ : Rel Carrier ℓ
    isProset : IsProset _≤_

IsProset⇒IsPartialOrder : ∀ {a ℓ} {A : Set a} {≤ : Rel A ℓ} →
  IsProset ≤ → IsPartialOrder (SymCore ≤) ≤
IsProset⇒IsPartialOrder {≤ = ≤} isProset = record
  { isPreorder = record
    { isEquivalence = record
      { refl = reflexive refl
      ; sym = symmetric
      ; trans = transitive trans
      }
    ; reflexive = holds
    ; trans = trans
    }
  ; antisym = _,_
  } where open IsProset isProset

Proset⇒Poset : Proset c ℓ → Poset c ℓ ℓ
Proset⇒Poset record { isProset = isProset } =
  record { isPartialOrder = IsProset⇒IsPartialOrder isProset }
