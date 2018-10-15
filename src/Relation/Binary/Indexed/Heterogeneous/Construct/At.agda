------------------------------------------------------------------------
-- The Agda standard library
--
-- Instantiates indexed binary structures at an index to the equivalent
-- non-indexed structures.
------------------------------------------------------------------------

module Relation.Binary.Indexed.Heterogeneous.Construct.At where

open import Relation.Binary
open import Relation.Binary.Indexed.Heterogeneous
  hiding (IsEquivalence; Setoid)

------------------------------------------------------------------------
-- Structures

module _ {a i} {I : Set i} {A : I → Set a} where

  isEquivalence : ∀ {ℓ} {_≈_ : IRel A ℓ} → IsIndexedEquivalence A _≈_ →
                  (index : I) → IsEquivalence (_≈_ {index})
  isEquivalence isEq index = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
    where open IsIndexedEquivalence isEq

  isPreorder : ∀ {ℓ₁ ℓ₂} {_≈_ : IRel A ℓ₁} {_∼_ : IRel A ℓ₂} →
               IsIndexedPreorder A _≈_ _∼_ →
               (index : I) → IsPreorder (_≈_ {index}) _∼_
  isPreorder isPreorder index = record
    { isEquivalence = isEquivalence O.isEquivalence index
    ; reflexive     = O.reflexive
    ; trans         = O.trans
    }
    where module O = IsIndexedPreorder isPreorder

------------------------------------------------------------------------
-- Packages

module _ {a i} {I : Set i} where

  setoid : ∀ {ℓ} → IndexedSetoid I a ℓ → I → Setoid a ℓ
  setoid S index = record
    { Carrier       = S.Carrier index
    ; _≈_           = S._≈_
    ; isEquivalence = isEquivalence S.isEquivalence index
    }
    where module S = IndexedSetoid S

  preorder : ∀ {ℓ₁ ℓ₂} → IndexedPreorder I a ℓ₁ ℓ₂ → I → Preorder a ℓ₁ ℓ₂
  preorder O index = record
    { Carrier    = O.Carrier index
    ; _≈_        = O._≈_
    ; _∼_        = O._∼_
    ; isPreorder = isPreorder O.isPreorder index
    }
    where module O = IndexedPreorder O

------------------------------------------------------------------------
-- Some useful shorthand infix notation

module _ {a i} {I : Set i} where

  _atₛ_ : ∀ {ℓ} → IndexedSetoid I a ℓ → I → Setoid a ℓ
  _atₛ_ = setoid
