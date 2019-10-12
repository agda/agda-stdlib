------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the polymorphic unit type
-- Defines Decidable Equality and Decidable Ordering as well
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit.Polymorphic.Properties where

open import Level
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Decidable Equality

infix 4 _≟_

_≟_ : {ℓ : Level} → Decidable {A = ⊤ {ℓ}} _≡_
_ ≟ _ = yes refl

------------------------------------------------------------------------
-- Setoid

≡-setoid : Setoid ℓ ℓ
≡-setoid = setoid ⊤

≡-decSetoid : DecSetoid ℓ ℓ
≡-decSetoid = decSetoid _≟_
