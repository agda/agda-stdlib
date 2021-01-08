------------------------------------------------------------------------
-- The Agda standard library
--
-- Instantiates the ring solver, using the natural numbers as the
-- coefficient "ring"
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
import Algebra.Properties.Semiring.Mult as SemiringMultiplication
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Data.Nat.Base as ℕ
open import Data.Product using (module Σ)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Algebra.Solver.Ring.NaturalCoefficients
  {r₁ r₂} (R : CommutativeSemiring r₁ r₂)
  (open CommutativeSemiring R)
  (open SemiringMultiplication semiring using () renaming (_×_ to _×ᵤ_))
  (dec : ∀ m n → Maybe (m ×ᵤ 1# ≈ n ×ᵤ 1#)) where

open import Algebra.Properties.Semiring.Mult.TCOptimised semiring

open import Relation.Binary.Reasoning.Setoid setoid

private

  -- The coefficient "ring".

  ℕ-ring : RawRing _ _
  ℕ-ring = record
    { Carrier = ℕ
    ; _≈_     = _≡_
    ; _+_     = ℕ._+_
    ; _*_     = ℕ._*_
    ; -_      = id
    ; 0#      = 0
    ; 1#      = 1
    }

  -- There is a homomorphism from ℕ to R.
  --
  -- Note that the optimised _×_ is used rather than unoptimised _×ᵤ_.
  -- If _×ᵤ_ were used, then Function.Related.TypeIsomorphisms.test would fail
  -- to type-check.

  homomorphism : ℕ-ring -Raw-AlmostCommutative⟶ fromCommutativeSemiring R
  homomorphism = record
    { ⟦_⟧    = λ n → n × 1#
    ; +-homo = ×-homo-+ 1#
    ; *-homo = ×1-homo-*
    ; -‿homo = λ _ → refl
    ; 0-homo = refl
    ; 1-homo = refl
    }

  -- Equality of certain expressions can be decided.

  dec′ : ∀ m n → Maybe (m × 1# ≈ n × 1#)
  dec′ m n = map to (dec m n)
    where
    to : m ×ᵤ 1# ≈ n ×ᵤ 1# → m × 1# ≈ n × 1#
    to m≈n = begin
      m ×  1#  ≈˘⟨ ×ᵤ≈× m 1# ⟩
      m ×ᵤ 1#  ≈⟨  m≈n ⟩
      n ×ᵤ 1#  ≈⟨  ×ᵤ≈× n 1# ⟩
      n ×  1#  ∎

-- The instantiation.

open import Algebra.Solver.Ring _ _ homomorphism dec′ public
