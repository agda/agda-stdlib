------------------------------------------------------------------------
-- The Agda standard library
--
-- Instantiates the ring solver with two copies of the same ring with
-- decidable equality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Solver.Ring.AlmostCommutativeRing using
  (AlmostCommutativeRing; -raw-almostCommutative⟶)
open import Relation.Binary.Definitions using (Decidable)

module Algebra.Solver.Ring.Simple
  {r₁ r₂} (R : AlmostCommutativeRing r₁ r₂)
  (_≟_ : Decidable (AlmostCommutativeRing._≈_ R))
  where

open import Relation.Binary.Consequences using (dec⇒weaklyDec)

open AlmostCommutativeRing R
import Algebra.Solver.Ring as RS
open RS rawRing R (-raw-almostCommutative⟶ R) (dec⇒weaklyDec _≟_) public
