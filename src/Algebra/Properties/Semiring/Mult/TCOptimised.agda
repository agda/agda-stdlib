------------------------------------------------------------------------
-- The Agda standard library
--
-- Multiplication over a semiring optimised for type-checking.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Data.Nat.Base as ℕ using (zero; suc)

module Algebra.Properties.Semiring.Mult.TCOptimised
  {a ℓ} (S : Semiring a ℓ) where

open Semiring S renaming (zero to *-zero)
open import Relation.Binary.Reasoning.Setoid setoid

open import Algebra.Properties.Semiring.Mult S as U
  using () renaming (_×_ to _×ᵤ_)

------------------------------------------------------------------------
-- Re-export definition from the monoid

open import Algebra.Properties.Monoid.Mult.TCOptimised +-monoid public

------------------------------------------------------------------------
-- Properties of _×_

-- (_×′ 1#) is homomorphic with respect to _ℕ.*_/_*_.

×1-homo-* : ∀ m n → (m ℕ.* n) × 1# ≈ (m × 1#) * (n × 1#)
×1-homo-* m n = begin
  (m ℕ.* n) ×  1#        ≈˘⟨ ×ᵤ≈× (m ℕ.* n) 1# ⟩
  (m ℕ.* n) ×ᵤ 1#        ≈⟨  U.×1-homo-* m n ⟩
  (m ×ᵤ 1#) * (n ×ᵤ 1#)  ≈⟨  *-cong (×ᵤ≈× m 1#) (×ᵤ≈× n 1#) ⟩
  (m ×  1#) * (n ×  1#)  ∎
