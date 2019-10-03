------------------------------------------------------------------------
-- The Agda standard library
--
-- The universe polymorphic unit type and the total relation on unit
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit.Polymorphic where

open import Level
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- A unit type defined as a record type

record ⊤ {ℓ : Level} : Set ℓ where
  constructor tt

------------------------------------------------------------------------
-- An ordering relation over the unit type

record _≤_ {ℓ ℓ′ e : Level} (x : ⊤ {ℓ}) (y : ⊤ {ℓ′}) : Set e where

------------------------------------------------------------------------
-- Decidable Equality and Ordering

infix 4 _≟_

_≟_ : {ℓ : Level} → Decidable {A = ⊤ {ℓ}} _≡_
_ ≟ _ = yes refl

infix 4 _≤?_

_≤?_ : {a b ℓ : Level} → Decidable {a} {_} {b} {ℓ = ℓ}  _≤_
_ ≤? _ = yes _
