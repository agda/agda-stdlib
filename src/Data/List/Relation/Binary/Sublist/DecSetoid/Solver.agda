------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for proving that one list is a sublist of the other.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (DecSetoid)

module Data.List.Relation.Binary.Sublist.DecSetoid.Solver {c ℓ} (S : DecSetoid c ℓ) where

open DecSetoid S

open import Data.List.Relation.Binary.Sublist.Heterogeneous.Solver _≈_ refl _≟_
  using (Item; module Item; TList; module TList; prove) public
