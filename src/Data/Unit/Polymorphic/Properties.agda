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
-- Decidable Equality and Ordering

infix 4 _≟_

_≟_ : {ℓ : Level} → Decidable {A = ⊤ {ℓ}} _≡_
_ ≟ _ = yes refl

------------------------------------------------------------------------
-- Setoid

≡-setoid : Setoid ℓ ℓ
≡-setoid = setoid ⊤

≡-decSetoid : DecSetoid ℓ ℓ
≡-decSetoid = decSetoid _≟_

------------------------------------------------------------------------
-- Relational properties

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
  ; antisym    = λ p _ → p
  }

≡-isTotalOrder : IsTotalOrder {ℓ} _≡_ _≡_
≡-isTotalOrder = record
  { isPartialOrder = ≡-isPartialOrder
  ; total          = λ _ _ → inj₁ refl
  }

≡-isDecTotalOrder : IsDecTotalOrder {ℓ} _≡_ _≡_
≡-isDecTotalOrder = record
  { isTotalOrder = ≡-isTotalOrder
  ; _≟_          = _≟_
  ; _≤?_         = _≟_
  }

-- Bundles

≡-poset : Poset ℓ ℓ ℓ
≡-poset = record
  { isPartialOrder = ≡-isPartialOrder
  }

≡-decTotalOrder : DecTotalOrder ℓ ℓ ℓ
≡-decTotalOrder = record
  { isDecTotalOrder = ≡-isDecTotalOrder
  }
