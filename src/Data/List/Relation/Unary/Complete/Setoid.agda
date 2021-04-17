------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists which contain every element of a given type
------------------------------------------------------------------------

open import Data.List
open import Level
open import Relation.Binary

module Data.List.Relation.Unary.Complete.Setoid
  {a ℓ} (S : Setoid a ℓ) where

open Setoid S renaming (Carrier to A)
open import Data.List.Membership.Setoid S

------------------------------------------------------------------------
-- Definition

Complete : List A → Set (a ⊔ ℓ)
Complete xs = ∀ x → x ∈ xs
