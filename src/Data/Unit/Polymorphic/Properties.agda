------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the polymorphic unit type
-- Defines Decidable Equality and Decidable Ordering as well
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit.Polymorphic.Properties where

open import Level
open import Data.Sum using (inj₁)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Equality
------------------------------------------------------------------------

infix 4 _≟_

_≟_ : Decidable {A = ⊤ {ℓ}} _≡_
_ ≟ _ = yes refl

≡-setoid : Setoid ℓ ℓ
≡-setoid = setoid ⊤

≡-decSetoid : DecSetoid ℓ ℓ
≡-decSetoid = decSetoid _≟_

------------------------------------------------------------------------
-- Ordering
------------------------------------------------------------------------

≡-total : Total {A = ⊤ {ℓ}} _≡_
≡-total _ _ = inj₁ refl

≡-antisym : Antisymmetric {A = ⊤ {ℓ}} _≡_ _≡_
≡-antisym p _ = p

------------------------------------------------------------------------
-- Structures

≡-isPreorder : IsPreorder {ℓ} {_} {⊤ {ℓ}} _≡_ _≡_
≡-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = λ x → x
  ; trans         = trans
  }

≡-isPartialOrder : IsPartialOrder {ℓ} _≡_ _≡_
≡-isPartialOrder = record
  { isPreorder = ≡-isPreorder
  ; antisym    = ≡-antisym
  }

≡-isTotalOrder : IsTotalOrder {ℓ} _≡_ _≡_
≡-isTotalOrder = record
  { isPartialOrder = ≡-isPartialOrder
  ; total          = ≡-total
  }

≡-isDecTotalOrder : IsDecTotalOrder {ℓ} _≡_ _≡_
≡-isDecTotalOrder = record
  { isTotalOrder = ≡-isTotalOrder
  ; _≟_          = _≟_
  ; _≤?_         = _≟_
  }

------------------------------------------------------------------------
-- Bundles

≡-poset : Poset ℓ ℓ ℓ
≡-poset = record
  { isPartialOrder = ≡-isPartialOrder
  }

≡-decTotalOrder : DecTotalOrder ℓ ℓ ℓ
≡-decTotalOrder = record
  { isDecTotalOrder = ≡-isDecTotalOrder
  }
