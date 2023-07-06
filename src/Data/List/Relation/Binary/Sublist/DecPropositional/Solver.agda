------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for proving that one list is a sublist of the other for types
-- which enjoy decidable equalities.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

module Data.List.Relation.Binary.Sublist.DecPropositional.Solver
       {a} {A : Set a} (_≟_ : Decidable {A = A} _≡_)
       where

import Relation.Binary.PropositionalEquality.Properties as P

open import Data.List.Relation.Binary.Sublist.DecSetoid.Solver (P.decSetoid _≟_) public
