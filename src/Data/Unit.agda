------------------------------------------------------------------------
-- The Agda standard library
--
-- Some unit types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit where

open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core

-- Some types are defined in Data.Unit.Base.

open import Data.Unit.Base public

------------------------------------------------------------------------
-- Operations

infix 4 _≟_ _≤?_

_≟_ : Decidable {A = ⊤} _≡_
_ ≟ _ = yes refl

_≤?_ : Decidable _≤_
_ ≤? _ = yes _

total : Total _≤_
total _ _ = inj₁ _

------------------------------------------------------------------------
-- Properties

setoid : Setoid _ _
setoid = record
  { isEquivalence = isEquivalence {A = ⊤}
  }

isPreorder : IsPreorder _≡_ _≤_
isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = _
  ; trans         = _
  }

isPartialOrder : IsPartialOrder _≡_ _≤_
isPartialOrder = record
  { isPreorder = isPreorder
  ; antisym    = λ _ _ → refl
  }

isTotalOrder : IsTotalOrder _≡_ _≤_
isTotalOrder = record
  { isPartialOrder = isPartialOrder
  ; total          = total
  }

isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
isDecTotalOrder = record
  { isTotalOrder = isTotalOrder
  ; _≟_          = _≟_
  ; _≤?_         = _≤?_
  }

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record
  { isDecTotalOrder = isDecTotalOrder
  }

decSetoid : DecSetoid _ _
decSetoid = DecTotalOrder.Eq.decSetoid decTotalOrder

poset : Poset _ _ _
poset = DecTotalOrder.poset decTotalOrder
