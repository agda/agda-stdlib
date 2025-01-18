------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable vector equality over propositional equality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Data.Vec.Relation.Binary.Equality.DecPropositional
  {a} {A : Set a} (_≟_ : DecidableEquality A) where

open import Data.Vec.Base using (Vec)
open import Data.Vec.Properties using (≡-dec)
import Data.Vec.Relation.Binary.Equality.Propositional as PEq
import Data.Vec.Relation.Binary.Equality.DecSetoid as DSEq
open import Relation.Binary.PropositionalEquality.Properties using (decSetoid)

------------------------------------------------------------------------
-- Publicly re-export everything from decSetoid and propositional
-- equality

open PEq public
open DSEq (decSetoid _≟_) public
  using (_≋?_; ≋-isDecEquivalence; ≋-decSetoid)

------------------------------------------------------------------------
-- Additional proofs

infix 4 _≡?_

_≡?_ : ∀ {n} → DecidableEquality (Vec A n)
_≡?_ = ≡-dec _≟_
