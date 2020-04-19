------------------------------------------------------------------------
-- The Agda standard library
--
-- Some specialised instances of the ring solver
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Tactic.RingSolver.Core.Polynomial.Parameters

-- Here, we provide proofs of homomorphism between the operations
-- defined on polynomials and those on the underlying ring.

module Tactic.RingSolver.Core.Polynomial.Homomorphism
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

-- The lemmas are the general-purpose proofs we reuse in each other section
open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Lemmas         homo using (pow-cong) public

-- Proofs for each component of the polynomial
open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Addition       homo using (⊞-hom) public
open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Multiplication homo using (⊠-hom) public
open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Negation       homo using (⊟-hom) public
open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Exponentiation homo using (⊡-hom) public
open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Constants      homo using (κ-hom) public
open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Variables      homo using (ι-hom) public
