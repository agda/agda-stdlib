------------------------------------------------------------------------
-- The Agda standard library
--
-- Another interface to the ring solver
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Maybe
open import Relation.Binary using (Decidable)
open import Relation.Nullary.Decidable using ()

module Tactics.RingSolver.Core.Simple
  {ℓ₁ ℓ₂} (ring : AlmostCommutativeRing ℓ₁ ℓ₂)
  (let open AlmostCommutativeRing ring)
  (_≟_ : Decidable _≈_)
  where

open import Tactics.RingSolver.Core.Solver ring (λ x → decToMaybe (0# ≟ x)) public
