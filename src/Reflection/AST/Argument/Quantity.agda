------------------------------------------------------------------------
-- The Agda standard library
--
-- Argument quantities used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.AST.Argument.Quantity where

open import Relation.Nullary                           using (yes; no)
open import Relation.Binary                            using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (refl)

------------------------------------------------------------------------
-- Re-exporting the builtins publicly

open import Agda.Builtin.Reflection public using (Quantity)
open Quantity public

------------------------------------------------------------------------
-- Decidable equality

infix 4 _≟_

_≟_ : DecidableEquality Quantity
quantity-ω ≟ quantity-ω = yes refl
quantity-0 ≟ quantity-0 = yes refl
quantity-ω ≟ quantity-0 = no λ()
quantity-0 ≟ quantity-ω = no λ()
