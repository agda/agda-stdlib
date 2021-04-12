------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of lists made up entirely of decidably unique elements
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.List
import Data.List.Relation.Unary.Unique.DecSetoid.Properties as Setoid
open import Data.List.Relation.Unary.All.Properties using (all-filter)
open import Level
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (decSetoid)

module Data.List.Relation.Unary.Unique.DecPropositional.Properties
  {a} {A : Set a} (_≟_ : DecidableEquality A) where

open import Data.List.Relation.Unary.Unique.DecPropositional _≟_

------------------------------------------------------------------------
-- Re-export propositional properties

open import Data.List.Relation.Unary.Unique.Propositional.Properties public

------------------------------------------------------------------------
-- deduplicate

deduplicate-! : ∀ xs → Unique (deduplicate _≟_ xs)
deduplicate-! = Setoid.deduplicate-! (decSetoid _≟_)
