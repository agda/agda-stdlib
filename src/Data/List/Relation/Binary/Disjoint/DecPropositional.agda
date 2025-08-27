------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidability of the disjoint relation over propositional equality.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Data.List.Relation.Binary.Disjoint.DecPropositional
  {a} {A : Set a} (_≟_ : DecidableEquality A)
  where

------------------------------------------------------------------------
-- Re-export core definitions and operations

open import Data.List.Relation.Binary.Disjoint.Propositional {A = A} public
open import Relation.Binary.PropositionalEquality.Properties using (decSetoid)
open import Data.List.Relation.Binary.Disjoint.DecSetoid (decSetoid _≟_) public
  using (disjoint?)
