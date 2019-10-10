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
open import Data.Unit.Polymorphic.Base using (⊤; tt; _≤_)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

private
  variable
    ℓ ℓ′ a b e : Level

------------------------------------------------------------------------
-- Decidable Equality and Ordering

infix 4 _≟_

_≟_ : {ℓ : Level} → Decidable {A = ⊤ {ℓ}} _≡_
_ ≟ _ = yes refl

infix 4 _≤?_

_≤?_ : {a b ℓ : Level} → Decidable {a} {_} {b} {ℓ = ℓ}  _≤_
_ ≤? _ = yes _

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

-- Bundles

≤-poset : Poset ℓ ℓ b
≤-poset = record
  { isPartialOrder = ≤-isPartialOrder
  }

≤-decTotalOrder : DecTotalOrder ℓ ℓ b
≤-decTotalOrder = record
  { isDecTotalOrder = ≤-isDecTotalOrder
  }
