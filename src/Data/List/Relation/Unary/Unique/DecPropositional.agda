------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists made up entirely of unique elements (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (DecSetoid; DecidableEquality)
open import Relation.Binary.PropositionalEquality using (decSetoid)
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Relation.Unary using (Decidable)
open import Relation.Nullary.Negation using (¬?)

module Data.List.Relation.Unary.Unique.DecPropositional
  {a} {A : Set a} (_≟_ : DecidableEquality A) where

------------------------------------------------------------------------
-- Re-export setoid definition

open import Data.List.Relation.Unary.Unique.DecSetoid (decSetoid _≟_) public
