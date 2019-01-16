------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable equality over lists using propositional equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.List
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

module Data.List.Relation.Equality.DecPropositional
  {a} {A : Set a} (_≟_ : Decidable {A = A} _≡_) where

import Data.List.Relation.Equality.Propositional as PropositionalEq
import Data.List.Relation.Equality.DecSetoid as DecSetoidEq

------------------------------------------------------------------------
-- Publically re-export everything from decSetoid and propositional
-- equality

open PropositionalEq public
open DecSetoidEq (decSetoid _≟_) public
  using (_≋?_; ≋-isDecEquivalence; ≋-decSetoid)

_≡?_ : Decidable (_≡_ {A = List A})
_≡?_ xs ys = map′ ≋⇒≡ ≡⇒≋ (_≋?_ xs ys)
