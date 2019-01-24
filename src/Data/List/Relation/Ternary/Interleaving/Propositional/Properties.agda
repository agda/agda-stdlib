------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of interleaving using propositional equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Ternary.Interleaving.Propositional.Properties
  {a} {A : Set a} where

import Data.List.Relation.Ternary.Interleaving.Setoid.Properties
  as SetoidProperties
open import Relation.Binary.PropositionalEquality using (setoid)

------------------------------------------------------------------------
-- Re-exporting existing properties

open SetoidProperties (setoid A) public
