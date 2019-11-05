------------------------------------------------------------------------
-- The Agda standard library
--
-- The unit type and the total relation on unit
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Agda.Builtin.Equality using (_≡_)

module Data.Unit.Base where

------------------------------------------------------------------------
-- A unit type defined as a record type

open import Agda.Builtin.Unit public
  using (⊤; tt)

-- Note that the name of this type is "\top", not T.


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.2

record _≤_ (x y : ⊤) : Set where
{-# WARNING_ON_USAGE _≤_
"Warning: _≤_ was deprecated in v1.2.
Please use _≡_ from Relation.Binary.PropositionalEquality instead."
#-}
