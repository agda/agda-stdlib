------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for proving that one list is a sublist of the other for
-- types which enjoy decidable equalities.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Data.List.Relation.Binary.Sublist.DecPropositional.Solver
       {a} {A : Set a} (_≟_ : DecidableEquality A)
       where

open import Relation.Binary.PropositionalEquality.Properties using (decSetoid)

open import Data.List.Relation.Binary.Sublist.DecSetoid.Solver (decSetoid _≟_) public
