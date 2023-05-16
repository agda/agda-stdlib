------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the unit type
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Unit.Properties where

open import Data.Sum.Base
open import Data.Unit.Base
open import Level using (0ℓ)
open import Relation.Nullary
open import Relation.Binary hiding (Irrelevant)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Irrelevancy

⊤-irrelevant : Irrelevant ⊤
⊤-irrelevant _ _ = refl

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
