------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for proving that one list is a sublist of the other.
------------------------------------------------------------------------

module Data.List.Relation.Sublist.Inductive.Propositional.Solver where

open import Relation.Binary.PropositionalEquality
import Data.List.Relation.Sublist.Inductive.Setoid.Solver as SubSolver
open module S {a} {A : Set a} = SubSolver (setoid A) public
