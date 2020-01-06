------------------------------------------------------------------------
-- The Agda standard library
--
-- Some specialised instances of the ring solver
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Construct.Polynomial.Parameters

-- Here, we provide proofs of homomorphism between the operations
-- defined on polynomials and those on the underlying ring.

module Algebra.Construct.Polynomial.Homomorphism
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

-- The lemmas are the general-purpose proofs we reuse in each other section
open import Algebra.Construct.Polynomial.Homomorphism.Lemmas         homo using (pow-cong) public

-- Proofs for each component of the polynomial
open import Algebra.Construct.Polynomial.Homomorphism.Addition       homo using (⊞-hom) public
open import Algebra.Construct.Polynomial.Homomorphism.Multiplication homo using (⊠-hom) public
open import Algebra.Construct.Polynomial.Homomorphism.Negation       homo using (⊟-hom) public
open import Algebra.Construct.Polynomial.Homomorphism.Exponentiation homo using (⊡-hom) public
open import Algebra.Construct.Polynomial.Homomorphism.Semantics      homo using (κ-hom; ι-hom) public
