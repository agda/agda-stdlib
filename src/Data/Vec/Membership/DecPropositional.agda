------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable propositional membership over vectors
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Data.Vec.Membership.DecPropositional
  {a} {A : Set a} (_≟_ : DecidableEquality A) where

open import Relation.Binary.PropositionalEquality.Properties using (decSetoid)

------------------------------------------------------------------------
-- Re-export contents of propositional membership

open import Data.Vec.Membership.Propositional {A = A} public
open import Data.Vec.Membership.DecSetoid (decSetoid _≟_) public
  using (_∈?_)
