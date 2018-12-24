------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of interleaving using propositional equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Interleaving.Propositional.Properties
  {a} {A : Set a} where

import Data.List.Relation.Interleaving.Setoid.Properties as SetoidProperties
open import Relation.Binary.PropositionalEquality using (setoid)

------------------------------------------------------------------------
-- Re-exporting existing properties

open SetoidProperties (setoid A) public
