------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional version of the sublist relation. This is commonly known
-- as an Order Preserving Embedding (OPE).
------------------------------------------------------------------------

module Data.List.Relation.Sublist.Inductive.Propositional where

open import Relation.Binary.PropositionalEquality
import Data.List.Relation.Sublist.Inductive.Setoid as Sublist

open module S {a} {A : Set a} = Sublist (setoid A) public
