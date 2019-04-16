------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists made up entirely of unique elements (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Data.List.Relation.Unary.Unique.Setoid {a ℓ} (S : Setoid a ℓ) where

open import Data.List
open import Data.List.Relation.Unary.AllPairs as AllPairsM
open import Level using (_⊔_)
open import Relation.Unary using (Pred)
open import Relation.Nullary using (¬_)

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition

Unique : Pred (List A) (a ⊔ ℓ)
Unique xs = AllPairs (λ x y → ¬ (x ≈ y)) xs

open AllPairsM public using (_∷_; []; head; tail)
