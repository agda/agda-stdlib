------------------------------------------------------------------------
-- The Agda standard library
--
-- Argument quantities used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Argument.Quantity where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Re-exporting the builtins publicly

open import Agda.Builtin.Reflection public using (Quantity)
open Quantity public

------------------------------------------------------------------------
-- Decidable equality

_≟_ : DecidableEquality Quantity
quantity-ω ≟ quantity-ω = yes refl
quantity-0 ≟ quantity-0 = yes refl
quantity-ω ≟ quantity-0 = no λ()
quantity-0 ≟ quantity-ω = no λ()
