------------------------------------------------------------------------
-- The Agda standard library
--
-- The unit type and the total relation on unit
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit.Base where

------------------------------------------------------------------------
-- A unit type defined as a record type

open import Agda.Builtin.Unit public
  using (⊤; tt)

-- Note that the name of this type is "\top", not T.

------------------------------------------------------------------------
-- An ordering relation over the unit type

record _≤_ (x y : ⊤) : Set where
