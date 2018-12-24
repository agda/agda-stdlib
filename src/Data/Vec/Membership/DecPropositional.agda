------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable propositional membership over vectors
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; decSetoid)

module Data.Vec.Membership.DecPropositional
  {a} {A : Set a} (_≟_ : Decidable (_≡_ {A = A})) where

------------------------------------------------------------------------
-- Re-export contents of propositional membership

open import Data.Vec.Membership.Propositional {A = A} public
open import Data.Vec.Membership.DecSetoid (decSetoid _≟_) public
  using (_∈?_)
