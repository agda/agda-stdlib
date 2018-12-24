------------------------------------------------------------------------
-- The Agda standard library
--
-- The sublist relation over propositional equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Subset.Propositional
  {a} {A : Set a} where

import Data.List.Relation.Subset.Setoid as SetoidSubset
open import Relation.Binary.PropositionalEquality using (setoid)

------------------------------------------------------------------------
-- Re-export parameterised definitions from setoid sublists

open SetoidSubset (setoid A) public
