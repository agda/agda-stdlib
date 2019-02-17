------------------------------------------------------------------------
-- The Agda standard library
--
-- Sublist-related properties for types with a decidable equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Decidable)
open import Agda.Builtin.Equality using (_≡_)

module Data.List.Relation.Binary.Sublist.DecPropositional.Properties
       {a} {A : Set a} (_≟_ : Decidable {A = A} _≡_)
       where

import Relation.Binary.PropositionalEquality as P

open import Data.List.Relation.Binary.Sublist.DecSetoid.Properties
  (P.decSetoid _≟_) public
open import Data.List.Relation.Binary.Sublist.Propositional.Properties {A = A}
  using (lookup-injective) public
