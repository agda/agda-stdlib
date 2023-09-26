------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable propositional membership over lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties using (decSetoid)

module Data.List.Membership.DecPropositional
  {a} {A : Set a} (_≟_ : Decidable (_≡_ {A = A})) where

------------------------------------------------------------------------
-- Re-export contents of propositional membership

open import Data.List.Membership.Propositional {A = A} public
open import Data.List.Membership.DecSetoid (decSetoid _≟_) public
  using (_∈?_; _∉?_)
