------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists which contain every element of a given type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.List
open import Level
open import Relation.Binary

module Data.List.Relation.Unary.Enumerates.Setoid
  {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)
open import Data.List.Membership.Setoid S

------------------------------------------------------------------------
-- Definition

IsEnumeration : List A → Set (a ⊔ ℓ)
IsEnumeration xs = ∀ x → x ∈ xs
