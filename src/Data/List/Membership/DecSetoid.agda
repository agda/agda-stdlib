------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable setoid membership over lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Nullary.Negation using (¬?)

module Data.List.Membership.DecSetoid {a ℓ} (DS : DecSetoid a ℓ) where

open import Data.List.Relation.Unary.Any using (any?)
open DecSetoid DS

------------------------------------------------------------------------
-- Re-export contents of propositional membership

open import Data.List.Membership.Setoid (DecSetoid.setoid DS) public

------------------------------------------------------------------------
-- Other operations

infix 4 _∈?_ _∉?_

_∈?_ : Decidable _∈_
x ∈? xs = any? (x ≟_) xs

_∉?_ : Decidable _∉_
x ∉? xs = ¬? (x ∈? xs)
