------------------------------------------------------------------------
-- The Agda standard library
--
-- Setoid membership over non-empty lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.NonEmpty.Membership.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Data.List.NonEmpty.Base using (List⁺)
open import Data.List.NonEmpty.Relation.Unary.Any using (Any)
open import Relation.Nullary.Negation using (¬_)

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definitions

infix 4 _∈_ _∉_

_∈_ : A → List⁺ A → Set _
x ∈ xs = Any (x ≈_) xs

_∉_ : A → List⁺ A → Set _
x ∉ xs = ¬ x ∈ xs
