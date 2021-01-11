------------------------------------------------------------------------
-- The Agda standard library
--
-- Multiplication by a natural number over a semiring
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Data.Nat.Base as ℕ using (zero; suc)

module Algebra.Properties.Semiring.Mult
  {a ℓ} (S : Semiring a ℓ) where

open Semiring S renaming (zero to *-zero)
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Re-export definition from the monoid

open import Algebra.Properties.Monoid.Mult +-monoid public

------------------------------------------------------------------------
-- Properties of _×_

-- (_× 1#) is homomorphic with respect to _ℕ.*_/_*_.

×1-homo-* : ∀ m n → (m ℕ.* n) × 1# ≈ (m × 1#) * (n × 1#)
×1-homo-* 0       n = sym (zeroˡ (n × 1#))
×1-homo-* (suc m) n = begin
  (n ℕ.+ m ℕ.* n) × 1#                ≈⟨  ×-homo-+ 1# n (m ℕ.* n) ⟩
  n × 1# + (m ℕ.* n) × 1#             ≈⟨  +-congˡ (×1-homo-* m n) ⟩
  n × 1# + (m × 1#) * (n × 1#)        ≈˘⟨ +-congʳ (*-identityˡ _) ⟩
  1# * (n × 1#) + (m × 1#) * (n × 1#) ≈˘⟨ distribʳ (n × 1#) 1# (m × 1#) ⟩
  (1# + m × 1#) * (n × 1#)            ∎
