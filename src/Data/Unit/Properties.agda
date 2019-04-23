------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the unit type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit.Properties where

open import Data.Sum
open import Data.Unit.Base
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; isEquivalence)

------------------------------------------------------------------------
-- Equality

infix 4 _≟_

_≟_ : Decidable {A = ⊤} _≡_
_ ≟ _ = yes refl

≡-setoid : Setoid _ _
≡-setoid = PropEq.setoid ⊤

≡-decSetoid : DecSetoid _ _
≡-decSetoid = record
  { isDecEquivalence = record
    { isEquivalence = isEquivalence
    ; _≟_           = _≟_
    }
  }

------------------------------------------------------------------------
-- _≤_

-- Relational properties

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive _ = _

≤-trans : Transitive _≤_
≤-trans _ _ = _

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym  _ _ = refl

≤-total : Total _≤_
≤-total _ _ = inj₁ _

infix 4 _≤?_

_≤?_ : Decidable _≤_
_ ≤? _ = yes _

-- Structures

≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = PropEq.isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder _≡_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym  = ≤-antisym
  }

≤-isTotalOrder : IsTotalOrder _≡_ _≤_
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total = ≤-total
  }

≤-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
≤-isDecTotalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  ; _≟_  = _≟_
  ; _≤?_ = _≤?_
  }

-- Packages

≤-poset : Poset _ _ _
≤-poset = record
  { isPartialOrder = ≤-isPartialOrder
  }

≤-decTotalOrder : DecTotalOrder _ _ _
≤-decTotalOrder = record
  { isDecTotalOrder = ≤-isDecTotalOrder
  }
