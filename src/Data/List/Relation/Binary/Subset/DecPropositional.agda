------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidability of the subset relation over propositional equality.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Data.List.Relation.Binary.Subset.DecPropositional
  {a} {A : Set a} (_≟_ : DecidableEquality A)
  where

------------------------------------------------------------------------
-- Re-export core definitions and operations

open import Data.List.Relation.Binary.Subset.Propositional {A = A} public
open import Relation.Binary.PropositionalEquality.Properties using (decSetoid)
open import Data.List.Relation.Binary.Subset.DecSetoid (decSetoid _≟_) public
  using (_⊆?_)
