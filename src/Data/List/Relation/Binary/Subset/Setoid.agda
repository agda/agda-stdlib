------------------------------------------------------------------------
-- The Agda standard library
--
-- The extensional sublist relation over setoid equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Subset.Setoid
  {c ℓ} (S : Setoid c ℓ) where

open import Data.List using (List)
open import Data.List.Membership.Setoid S using (_∈_)
open import Level using (_⊔_)
open import Relation.Nullary using (¬_)

open Setoid S renaming (Carrier to A)

------------------------------------------------------------------------
-- Definitions

infix 4 _⊆_ _⊈_

_⊆_ : Rel (List A) (c ⊔ ℓ)
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

_⊈_ : Rel (List A) (c ⊔ ℓ)
xs ⊈ ys = ¬ xs ⊆ ys
