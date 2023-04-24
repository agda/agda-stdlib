------------------------------------------------------------------------
-- The Agda standard library
--
-- Interleavings of lists using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary using (Setoid)

module Data.List.Relation.Ternary.Interleaving.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Level using (_⊔_)
open import Data.List.Base as List using (List)
import Data.List.Relation.Ternary.Interleaving as General
open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition

Interleaving : List A → List A → List A → Set (c ⊔ ℓ)
Interleaving = General.Interleaving _≈_ _≈_

------------------------------------------------------------------------
-- Re-export the basic combinators

open General hiding (Interleaving) public
