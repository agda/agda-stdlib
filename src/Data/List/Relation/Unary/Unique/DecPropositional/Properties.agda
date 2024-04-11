------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of lists made up entirely of decidably unique elements
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Data.List.Relation.Unary.Unique.DecPropositional.Properties
  {a} {A : Set a} (_≟_ : DecidableEquality A) where

open import Data.List.Base using (deduplicate)
open import Data.List.Relation.Unary.All.Properties using (all-filter)
open import Data.List.Relation.Unary.Unique.DecPropositional _≟_
import Data.List.Relation.Unary.Unique.DecSetoid.Properties as Setoid
open import Level
open import Relation.Binary.PropositionalEquality.Properties using (decSetoid)

------------------------------------------------------------------------
-- Re-export propositional properties

open import Data.List.Relation.Unary.Unique.Propositional.Properties public

------------------------------------------------------------------------
-- deduplicate

deduplicate-! : ∀ xs → Unique (deduplicate _≟_ xs)
deduplicate-! = Setoid.deduplicate-! (decSetoid _≟_)
