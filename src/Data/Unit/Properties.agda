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
