------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists made up entirely of unique elements (propositional equality)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Unary.Unique.Propositional {a} {A : Set a} where

open import Relation.Binary.PropositionalEquality.Properties using (setoid)

------------------------------------------------------------------------
-- Re-export the contents of setoid uniqueness

open import Data.List.Relation.Unary.Unique.Setoid (setoid A) public

