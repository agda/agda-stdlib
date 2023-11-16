------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of lists made up entirely of decidably unique elements
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.List.Base using ([]; _∷_; deduplicate)
import Data.List.Relation.Unary.Unique.DecSetoid as Unique
open import Data.List.Relation.Unary.All.Properties using (all-filter)
open import Data.List.Relation.Unary.Unique.Setoid.Properties
open import Level
open import Relation.Binary.Bundles using (DecSetoid)

module Data.List.Relation.Unary.Unique.DecSetoid.Properties where

private
  variable
    a ℓ : Level

------------------------------------------------------------------------
-- deduplicate

module _ (DS : DecSetoid a ℓ) where

  open DecSetoid DS renaming (setoid to S)
  open Unique DS

  deduplicate-! : ∀ xs → Unique (deduplicate _≟_ xs)
  deduplicate-! []       = []
  deduplicate-! (x ∷ xs) = all-filter _ (deduplicate _≟_ xs) ∷ filter⁺ S _ (deduplicate-! xs)
