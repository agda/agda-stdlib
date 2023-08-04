------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists made up entirely of unique elements (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary using (DecSetoid; DecidableEquality)
open import Relation.Binary.PropositionalEquality.Properties using (decSetoid)

module Data.List.Relation.Unary.Unique.DecPropositional
  {a} {A : Set a} (_≟_ : DecidableEquality A) where

------------------------------------------------------------------------
-- Re-export setoid definition

open import Data.List.Relation.Unary.Unique.DecSetoid (decSetoid _≟_) public
