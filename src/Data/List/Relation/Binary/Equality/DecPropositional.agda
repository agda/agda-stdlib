------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable pointwise equality over lists using propositional equality
------------------------------------------------------------------------

-- Note think carefully about using this module as pointwise
-- propositional equality can usually be replaced with propositional
-- equality.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Data.List.Relation.Binary.Equality.DecPropositional
  {a} {A : Set a} (_≟_ : Decidable {A = A} _≡_) where

open import Data.List.Base using (List)
open import Data.List.Properties using (≡-dec)
import Data.List.Relation.Binary.Equality.Propositional as PropositionalEq
import Data.List.Relation.Binary.Equality.DecSetoid as DecSetoidEq

------------------------------------------------------------------------
-- Publically re-export everything from decSetoid and propositional
-- equality

open PropositionalEq public
open DecSetoidEq (decSetoid _≟_) public
  using (_≋?_; ≋-isDecEquivalence; ≋-decSetoid)

------------------------------------------------------------------------
-- Additional proofs

_≡?_ : Decidable (_≡_ {A = List A})
_≡?_ = ≡-dec _≟_
