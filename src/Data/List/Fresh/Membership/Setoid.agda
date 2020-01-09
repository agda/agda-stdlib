------------------------------------------------------------------------
-- The Agda standard library
--
-- Membership predicate for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Fresh.Membership.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Level using (Level; _⊔_)
open import Data.List.Fresh
open import Data.List.Fresh.Relation.Unary.Any as Any using (Any)
open import Relation.Nullary

open Setoid S renaming (Carrier to A)

private
  variable
    r : Level

_∈_ : {R : Rel A r} → A → List# A R → Set _
x ∈ xs = Any (x ≈_) xs

_∉_ : {R : Rel A r} → A → List# A R → Set _
x ∉ xs = ¬ (x ∈ xs)
