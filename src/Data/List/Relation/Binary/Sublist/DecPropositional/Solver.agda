------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for proving that one list is a sublist of the other for types
-- which enjoy decidable equalities.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Decidable)
open import Agda.Builtin.Equality using (_≡_)

module Data.List.Relation.Binary.Sublist.DecPropositional.Solver
       {a} {A : Set a} (_≟_ : Decidable {A = A} _≡_)
       where

import Relation.Binary.PropositionalEquality as P

open import Data.List.Relation.Binary.Sublist.DecSetoid.Solver (P.decSetoid _≟_) public
