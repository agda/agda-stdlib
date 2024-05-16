------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable vector equality over propositional equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Data.Vec.Relation.Binary.Equality.DecPropositional
  {a} {A : Set a} (_≟_ : DecidableEquality A) where

import Data.Vec.Relation.Binary.Equality.Propositional as PEq
import Data.Vec.Relation.Binary.Equality.DecSetoid as DSEq
open import Relation.Binary.PropositionalEquality.Properties using (decSetoid)

------------------------------------------------------------------------
-- Publicly re-export everything from decSetoid and propositional
-- equality

open PEq public
open DSEq (decSetoid _≟_) public
  using (_≋?_; ≋-isDecEquivalence; ≋-decSetoid)
