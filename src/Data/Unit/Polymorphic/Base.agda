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
