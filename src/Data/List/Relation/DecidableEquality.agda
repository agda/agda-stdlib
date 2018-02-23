------------------------------------------------------------------------
-- The Agda standard library
--
-- Decidable equality over lists parameterised by some DecSetoid
------------------------------------------------------------------------

open import Relation.Binary using (DecSetoid)

module Data.List.Relation.DecidableEquality
  {a ℓ} (DS : DecSetoid a ℓ) where

import Data.List.Relation.Equality as Equality
import Data.List.Relation.Pointwise as PW
open import Relation.Binary using (Decidable)
open DecSetoid DS

------------------------------------------------------------------------
-- Make all definitions from equality available

open Equality setoid public

------------------------------------------------------------------------
-- Additional properties

_≋?_ : Decidable _≋_
_≋?_ = PW.decidable _≟_
