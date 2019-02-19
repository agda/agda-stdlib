------------------------------------------------------------------------
-- The Agda standard library
--
-- Instantiates the ring solver, using the natural numbers as the
-- coefficient "ring"
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
import Algebra.Operations.Semiring as SemiringOps
open import Data.Maybe.Base using (Maybe; just; nothing; map)

module Algebra.Solver.Ring.NaturalCoefficients
         {r₁ r₂}
         (R : CommutativeSemiring r₁ r₂)
         (dec : let open CommutativeSemiring R
                    open SemiringOps semiring in
                ∀ m n → Maybe (m × 1# ≈ n × 1#)) where

import Algebra.Solver.Ring
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Data.Nat.Base as ℕ
open import Data.Product using (module Σ)
open import Function

open CommutativeSemiring R
open SemiringOps semiring
open import Relation.Binary.Reasoning.Setoid setoid

private

  AR = fromCommutativeSemiring R

  -- The coefficient "ring".

  ℕ-ring : RawRing _
  ℕ-ring = record
    { Carrier = ℕ
    ; _+_     = ℕ._+_
    ; _*_     = ℕ._*_
    ; -_      = id
    ; 0#      = 0
    ; 1#      = 1
    }

  -- There is a homomorphism from ℕ to R.
  --
  -- Note that _×′_ is used rather than _×_. If _×_ were used, then
  -- Function.Related.TypeIsomorphisms.test would fail to type-check.

  homomorphism :
    ℕ-ring -Raw-AlmostCommutative⟶ AR
  homomorphism = record
    { ⟦_⟧    = λ n → n ×′ 1#
    ; +-homo = ×′-homo-+ 1#
    ; *-homo = ×′1-homo-*
    ; -‿homo = λ _ → refl
    ; 0-homo = refl
    ; 1-homo = refl
    }

  -- Equality of certain expressions can be decided.

  dec′ : ∀ m n → Maybe (m ×′ 1# ≈ n ×′ 1#)
  dec′ m n = map to (dec m n)
    where
    to : m × 1# ≈ n × 1# → m ×′ 1# ≈ n ×′ 1#
    to m≈n = begin
      m ×′ 1#  ≈⟨ sym $ ×≈×′ m 1# ⟩
      m ×  1#  ≈⟨ m≈n ⟩
      n ×  1#  ≈⟨ ×≈×′ n 1# ⟩
      n ×′ 1#  ∎

-- The instantiation.

open Algebra.Solver.Ring ℕ-ring AR homomorphism dec′ public
