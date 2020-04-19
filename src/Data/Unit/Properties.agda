------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the unit type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from deprecation warnings for _≤_
{-# OPTIONS --warn=noUserWarning #-}

module Data.Unit.Properties where

open import Data.Sum.Base
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
-- Relational properties

≡-total : Total {A = ⊤} _≡_
≡-total _ _ = inj₁ refl

≡-antisym : Antisymmetric {A = ⊤} _≡_ _≡_
≡-antisym eq _ = eq

------------------------------------------------------------------------
-- Structures

≡-isPreorder : IsPreorder {A = ⊤} _≡_ _≡_
≡-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = λ x → x
  ; trans         = trans
  }

≡-isPartialOrder : IsPartialOrder _≡_ _≡_
≡-isPartialOrder = record
  { isPreorder = ≡-isPreorder
  ; antisym    = ≡-antisym
  }

≡-isTotalOrder : IsTotalOrder _≡_ _≡_
≡-isTotalOrder = record
  { isPartialOrder = ≡-isPartialOrder
  ; total          = ≡-total
  }

≡-isDecTotalOrder : IsDecTotalOrder _≡_ _≡_
≡-isDecTotalOrder = record
  { isTotalOrder = ≡-isTotalOrder
  ; _≟_          = _≟_
  ; _≤?_         = _≟_
  }

------------------------------------------------------------------------
-- Bundles

≡-poset : Poset 0ℓ 0ℓ 0ℓ
≡-poset = record
  { isPartialOrder = ≡-isPartialOrder
  }

≡-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ
≡-decTotalOrder = record
  { isDecTotalOrder = ≡-isDecTotalOrder
  }

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.2

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive _ = _
{-# WARNING_ON_USAGE ≤-reflexive
"Warning: ≤-reflexive was deprecated in v1.2.
Please use id from Function instead."
#-}
≤-trans : Transitive _≤_
≤-trans _ _ = _
{-# WARNING_ON_USAGE ≤-trans
"Warning: ≤-trans was deprecated in v1.2.
Please use trans from Relation.Binary.PropositionalEquality instead."
#-}
≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym  _ _ = refl
{-# WARNING_ON_USAGE ≤-antisym
"Warning: ≤-antisym was deprecated in v1.2.
Please use ≡-antisym instead."
#-}
≤-total : Total _≤_
≤-total _ _ = inj₁ _
{-# WARNING_ON_USAGE ≤-total
"Warning: ≤-total was deprecated in v1.2.
Please use ≡-total instead."
#-}
infix 4 _≤?_
_≤?_ : Decidable _≤_
_ ≤? _ = yes _
{-# WARNING_ON_USAGE _≤?_
"Warning: _≤_ was deprecated in v1.2.
Please use _≟_  instead."
#-}
≤-isPreorder : IsPreorder _≡_ _≤_
≤-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }
{-# WARNING_ON_USAGE ≤-isPreorder
"Warning: ≤-isPreorder was deprecated in v1.2.
Please use ≡-isPreorder instead."
#-}
≤-isPartialOrder : IsPartialOrder _≡_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }
{-# WARNING_ON_USAGE ≤-isPartialOrder
"Warning: ≤-isPartialOrder was deprecated in v1.2.
Please use ≡-isPartialOrder instead."
#-}
≤-isTotalOrder : IsTotalOrder _≡_ _≤_
≤-isTotalOrder = record
  { isPartialOrder = ≤-isPartialOrder
  ; total          = ≤-total
  }
{-# WARNING_ON_USAGE ≤-isTotalOrder
"Warning: ≤-isTotalOrder was deprecated in v1.2.
Please use ≡-isTotalOrder instead."
#-}
≤-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_
≤-isDecTotalOrder = record
  { isTotalOrder = ≤-isTotalOrder
  ; _≟_          = _≟_
  ; _≤?_         = _≤?_
  }
{-# WARNING_ON_USAGE ≤-isDecTotalOrder
"Warning: ≤-isDecTotalOrder was deprecated in v1.2.
Please use ≡-isDecTotalOrder instead."
#-}

-- Bundles

≤-poset : Poset 0ℓ 0ℓ 0ℓ
≤-poset = record
  { isPartialOrder = ≤-isPartialOrder
  }
{-# WARNING_ON_USAGE ≤-poset
"Warning: ≤-poset was deprecated in v1.2.
Please use ≡-poset instead."
#-}
≤-decTotalOrder : DecTotalOrder 0ℓ 0ℓ 0ℓ
≤-decTotalOrder = record
  { isDecTotalOrder = ≤-isDecTotalOrder
  }
{-# WARNING_ON_USAGE ≤-decTotalOrder
"Warning: ≤-decTotalOrder was deprecated in v1.2.
Please use ≡-decTotalOrder instead."
#-}
