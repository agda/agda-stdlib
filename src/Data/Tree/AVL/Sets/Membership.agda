------------------------------------------------------------------------
-- The Agda standard library
--
-- Membership relation for AVL sets
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.Tree.AVL.Sets.Membership
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Bool.Base using (true; false)
open import Data.Product as Prod using (_,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_)
open import Data.Unit.Base using (tt)
open import Function.Base using (_∘_; _∘′_; const)

open import Relation.Nullary using (¬_; yes; no; Reflects)
open import Relation.Nullary.Reflects using (fromEquivalence)

open StrictTotalOrder strictTotalOrder renaming (Carrier to A)
open import Data.Tree.AVL.Sets strictTotalOrder
open import Data.Tree.AVL.Map.Relation.Unary.Any strictTotalOrder as Mapₚ

------------------------------------------------------------------------
-- ∈

infix 4 _∈_ _∉_

_∈_ : A → ⟨Set⟩ → Set _
x ∈ s = Any ((x ≈_) ∘ proj₁) s

_∉_ : A → ⟨Set⟩ → Set _
x ∉ s = ¬ x ∈ s
