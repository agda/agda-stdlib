------------------------------------------------------------------------
-- The Agda standard library
--
-- Instantiates the ring solver with two copies of the same ring with
-- decidable equality
------------------------------------------------------------------------

open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Relation.Binary
open import Relation.Binary.Consequences using (dec⟶weaklyDec)

module Algebra.Solver.Ring.Simple
         {r₁ r₂} (R : AlmostCommutativeRing r₁ r₂)
         (_≟_ : Decidable (AlmostCommutativeRing._≈_ R))
         where

open AlmostCommutativeRing R
import Algebra.Solver.Ring as RS
open RS rawRing R (-raw-almostCommutative⟶ R) (dec⟶weaklyDec _≟_) public
