------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable equality over lists parameterised by some setoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.List.Relation.Binary.Equality.DecSetoid
  {a ℓ} (DS : DecSetoid a ℓ) where

import Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
import Data.List.Relation.Binary.Pointwise as PW
open import Level
open import Relation.Binary using (Decidable)
open DecSetoid DS

------------------------------------------------------------------------
-- Make all definitions from setoid equality available

open SetoidEquality setoid public

------------------------------------------------------------------------
-- Additional properties

infix 4 _≋?_

_≋?_ : Decidable _≋_
_≋?_ = PW.decidable _≟_

≋-isDecEquivalence : IsDecEquivalence _≋_
≋-isDecEquivalence = PW.isDecEquivalence isDecEquivalence

≋-decSetoid : DecSetoid a (a ⊔ ℓ)
≋-decSetoid = PW.decSetoid DS
