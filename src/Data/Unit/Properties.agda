------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the unit type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit.Properties where

open import Data.Sum
open import Data.Unit.Base
open import Level using (0ℓ)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Equality

infix 4 _≟_

_≟_ : Decidable {A = ⊤} _≡_
_ ≟ _ = yes refl

≡-setoid : Setoid 0ℓ 0ℓ
≡-setoid = setoid ⊤

≡-decSetoid : DecSetoid 0ℓ 0ℓ
≡-decSetoid = decSetoid _≟_

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
  { isEquivalence = isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

≤-isPartialOrder : IsPartialOrder _≡_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-isTotalOrder : IsTotalOrder _≡_ _≤_
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total          = ≤-total
  }

≤-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
≤-isDecTotalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  ; _≟_          = _≟_
  ; _≤?_         = _≤?_
  }

-- Packages

≤-poset : Poset 0ℓ 0ℓ 0ℓ
≤-poset = record
  { isPartialOrder = ≤-isPartialOrder
  }

≤-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ
≤-decTotalOrder = record
  { isDecTotalOrder = ≤-isDecTotalOrder
  }
