------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists made up entirely of unique elements (propositional equality)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.Unique.Propositional {a} {A : Set a} where

open import Relation.Binary.PropositionalEquality using (setoid)
open import Data.List.Relation.Unary.Unique.Setoid as SetoidUnique

------------------------------------------------------------------------
-- Re-export the contents of setoid uniqueness

open SetoidUnique (setoid A) public

