------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists made up entirely of unique elements (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (DecSetoid)
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Relation.Unary using (Decidable)
open import Relation.Nullary.Negation using (¬?)

module Data.List.Relation.Unary.Unique.DecSetoid
  {a ℓ} (DS : DecSetoid a ℓ) where

open DecSetoid DS renaming (setoid to S)

------------------------------------------------------------------------
-- Re-export setoid definition

open import Data.List.Relation.Unary.Unique.Setoid S public

------------------------------------------------------------------------
-- Additional properties

unique? : Decidable Unique
unique? = AllPairs.allPairs? (λ x y → ¬? (x ≟ y))
