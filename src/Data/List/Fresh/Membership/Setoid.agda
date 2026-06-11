------------------------------------------------------------------------
-- The Agda standard library
--
-- Membership predicate for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Fresh.Membership.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Level using (Level)
open import Data.List.Fresh using (List#)
open import Data.List.Fresh.Relation.Unary.Any as Any using (Any)
open import Relation.Binary.Core using (Rel; REL)
open import Relation.Nullary.Negation.Core using (¬_)

open Setoid S
  using (_≈_)
  renaming (Carrier to A)

private
  variable
    r : Level
    R : Rel A r


infix 4 _∈_ _∉_

_∈_ : REL A (List# A R) _
x ∈ xs = Any (x ≈_) xs

_∉_ : REL A (List# A R) _
x ∉ xs = ¬ (x ∈ xs)
