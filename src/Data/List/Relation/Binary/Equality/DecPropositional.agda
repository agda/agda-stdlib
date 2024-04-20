------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable pointwise equality over lists using propositional equality
------------------------------------------------------------------------

-- Note think carefully about using this module as pointwise
-- propositional equality can usually be replaced with propositional
-- equality.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Data.List.Relation.Binary.Equality.DecPropositional
  {a} {A : Set a} (_≟_ : DecidableEquality A) where

open import Data.List.Base using (List)
open import Data.List.Properties using (≡-dec)
import Data.List.Relation.Binary.Equality.Propositional as PropositionalEq
import Data.List.Relation.Binary.Equality.DecSetoid as DecSetoidEq
open import Relation.Binary.PropositionalEquality.Properties using (decSetoid)

------------------------------------------------------------------------
-- Publically re-export everything from decSetoid and propositional
-- equality

open PropositionalEq public
open DecSetoidEq (decSetoid _≟_) public
  using (_≋?_; ≋-isDecEquivalence; ≋-decSetoid)

------------------------------------------------------------------------
-- Additional proofs

infix 4 _≡?_

_≡?_ : DecidableEquality (List A)
_≡?_ = ≡-dec _≟_
