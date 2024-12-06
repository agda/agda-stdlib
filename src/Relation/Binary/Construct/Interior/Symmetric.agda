------------------------------------------------------------------------
-- The Agda standard library
--
-- Symmetric interior of a binary relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.Interior.Symmetric where

open import Data.Bool.Base using (_∧_)
open import Function.Base using (flip; _∘_)
open import Level using (Level)
open import Relation.Binary
open import Relation.Nullary.Decidable.Core
open import Relation.Nullary.Reflects

private
  variable
    a ℓ : Level
    A : Set a
    R S T : Rel A ℓ

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

-- Decidability
decidable : Decidable R → Decidable (SymInterior R)
does  (decidable R? x y) = does (R? x y) ∧ does (R? y x)
proof (decidable R? x y) = proof (R? x y) reflects proof (R? y x)
  where
  _reflects_ : ∀ {bxy byx} → Reflects (R x y) bxy → Reflects (R y x) byx →
               Reflects (SymInterior R x y) (bxy ∧ byx)
  ofʸ rxy  reflects ofʸ ryx  = of (rxy , ryx)
  ofʸ rxy  reflects ofⁿ ¬ryx = of (¬ryx ∘ rhs≤lhs)
  ofⁿ ¬rxy reflects _        = of (¬rxy ∘ lhs≤rhs)

-- A reflexive transitive relation _≤_ gives rise to a poset in which the
-- equivalence relation is SymInterior _≤_.

module _ {R : Rel A ℓ} (refl : Reflexive R) (trans : Transitive R) where

  isEquivalence : IsEquivalence (SymInterior R)
  isEquivalence = record
    { refl = reflexive refl
    ; sym = symmetric
    ; trans = transitive trans
    }

  isPreorder : IsPreorder (SymInterior R) R
  isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive = lhs≤rhs
    ; trans = trans
    }

  isPartialOrder : IsPartialOrder (SymInterior R) R
  isPartialOrder = record
    { isPreorder = isPreorder
    ; antisym = _,_
    }

  poset : Poset _ ℓ ℓ
  poset = record { isPartialOrder = isPartialOrder }

  module _ (R? : Decidable R) where

    isDecPartialOrder : IsDecPartialOrder (SymInterior R) R
    isDecPartialOrder = record
      { isPartialOrder = isPartialOrder
      ; _≟_ = decidable R?
      ; _≤?_ = R?
      }

    decPoset : DecPoset _ ℓ ℓ
    decPoset = record { isDecPartialOrder = isDecPartialOrder }

    open DecPoset public
      using (isDecPreorder; decPreorder)

    isDecEquivalence : IsDecEquivalence (SymInterior R)
    isDecEquivalence = DecPoset.Eq.isDecEquivalence decPoset

