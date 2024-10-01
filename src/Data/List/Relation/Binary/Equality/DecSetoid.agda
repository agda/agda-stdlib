------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise decidable equality over lists parameterised by a setoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (DecSetoid)

module Data.List.Relation.Binary.Equality.DecSetoid
  {a ℓ} (DS : DecSetoid a ℓ) where

import Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
open import Data.List.Relation.Binary.Pointwise using (decSetoid)

------------------------------------------------------------------------
-- Additional properties

≋-decSetoid : DecSetoid _ _
≋-decSetoid = decSetoid DS

open DecSetoid ≋-decSetoid public
  using (setoid)
  renaming (isDecEquivalence to ≋-isDecEquivalence; _≟_ to _≋?_)

------------------------------------------------------------------------
-- Make all definitions from setoid equality available

open SetoidEquality setoid public
