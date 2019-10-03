------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the polymorphic unit type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit.Polymorphic.Properties where

open import Data.Sum
open import Data.Unit.Polymorphic
open import Level
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

private
  variable
    ℓ ℓ′ a b e : Level

------------------------------------------------------------------------
-- Setoid

≡-setoid : Setoid ℓ ℓ
≡-setoid = setoid ⊤

≡-decSetoid : DecSetoid ℓ ℓ
≡-decSetoid = decSetoid _≟_

------------------------------------------------------------------------
-- _≤_

-- Relational properties

≤-reflexive : _≡_ {a} ⇒ (_≤_ {e = e})
≤-reflexive _ = _

≤-trans : Transitive (_≤_ {ℓ} {e = e})
≤-trans _ _ = _

≤-antisym : Antisymmetric _≡_ (_≤_ {ℓ} {e = e})
≤-antisym  _ _ = refl

≤-total : Total (_≤_ {ℓ} {e = e})
≤-total _ _ = inj₁ _


-- Structures

≤-isPreorder : IsPreorder _≡_ (_≤_ {ℓ} {e = e})
≤-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder _≡_ (_≤_ {ℓ} {e = e})
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-isTotalOrder : IsTotalOrder _≡_ (_≤_ {ℓ} {e = e})
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total          = ≤-total
  }

≤-isDecTotalOrder : IsDecTotalOrder _≡_ (_≤_ {ℓ} {e = e})
≤-isDecTotalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  ; _≟_          = _≟_
  ; _≤?_         = _≤?_
  }

-- Packages

≤-poset : Poset ℓ ℓ b
≤-poset = record
  { isPartialOrder = ≤-isPartialOrder
  }

≤-decTotalOrder : DecTotalOrder ℓ ℓ b
≤-decTotalOrder = record
  { isDecTotalOrder = ≤-isDecTotalOrder
  }
