------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable propositional membership over lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Data.List.Membership.DecPropositional
  {a} {A : Set a} (_≟_ : DecidableEquality A) where

open import Relation.Binary.PropositionalEquality.Properties using (decSetoid)

open import Relation.Binary.PropositionalEquality.Properties using (decSetoid)

------------------------------------------------------------------------
-- Re-export contents of propositional membership

open import Data.List.Membership.Propositional {A = A} public
open import Data.List.Membership.DecSetoid (decSetoid _≟_) public
  using (_∈?_; _∉?_)
