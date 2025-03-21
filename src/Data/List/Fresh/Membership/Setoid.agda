------------------------------------------------------------------------
-- The Agda standard library
--
-- Membership predicate for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Fresh.Membership.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Level using (Level; _⊔_)
open import Data.List.Fresh using (List#)
open import Data.List.Fresh.Relation.Unary.Any as Any using (Any)
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary.Negation.Core using (¬_)

open Setoid S renaming (Carrier to A)

infix 4 _∈_ _∉_

private
  variable
    r : Level

_∈_ : {R : Rel A r} → A → List# A R → Set _
x ∈ xs = Any (x ≈_) xs

_∉_ : {R : Rel A r} → A → List# A R → Set _
x ∉ xs = ¬ (x ∈ xs)
