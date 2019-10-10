------------------------------------------------------------------------
-- The Agda standard library
--
-- The universe polymorphic unit type and ordering relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit.Polymorphic.Base where

open import Level

------------------------------------------------------------------------
-- A unit type defined as a record type

record ⊤ {ℓ : Level} : Set ℓ where
  constructor tt

------------------------------------------------------------------------
-- An ordering relation over the unit type

record _≤_ {ℓ ℓ′ e : Level} (x : ⊤ {ℓ}) (y : ⊤ {ℓ′}) : Set e where
