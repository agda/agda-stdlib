------------------------------------------------------------------------
-- The Agda standard library
--
-- Appending of lists using setoid equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Data.List.Relation.Ternary.Appending.Setoid
  {c ℓ} (S : Setoid c ℓ)
  where

open import Level using (_⊔_)
open import Data.List.Base as List using (List)
import Data.List.Relation.Ternary.Appending as General
open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition

Appending : List A → List A → List A → Set (c ⊔ ℓ)
Appending = General.Appending _≈_ _≈_

------------------------------------------------------------------------
-- Re-export the basic combinators

open General public
  hiding (Appending)
