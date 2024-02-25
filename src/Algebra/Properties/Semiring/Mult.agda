------------------------------------------------------------------------
-- The Agda standard library
--
-- Multiplication by a natural number over a semiring
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Semiring)
open import Data.Nat.Base as ℕ using (zero; suc)

module Algebra.Properties.Semiring.Mult
  {a ℓ} (S : Semiring a ℓ) where

open Semiring S renaming (zero to *-zero)
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Definitions _≈_ using (_IdempotentOn_)

------------------------------------------------------------------------
-- Re-export definition from the monoid

open import Algebra.Properties.Monoid.Mult +-monoid public

------------------------------------------------------------------------
-- Properties of _×_

-- (0 ×_) is (0# *_)

×-homo-0# : ∀ x → 0 × x ≈ 0# * x
×-homo-0# x = sym (zeroˡ x)

-- (1 ×_) is (1# *_)

×-homo-1# : ∀ x → 1 × x ≈ 1# * x
×-homo-1# x = trans (×-homo-1 x) (sym (*-identityˡ x))

-- (n ×_) commutes with _*_

×-comm-* : ∀ n x y → x * (n × y) ≈ n × (x * y)
×-comm-* zero    x y = zeroʳ x
×-comm-* (suc n) x y = begin
  x * (suc n × y)       ≡⟨⟩
  x * (y + n × y)       ≈⟨ distribˡ _ _ _ ⟩
  x * y + x * (n × y)   ≈⟨ +-congˡ (×-comm-* n _ _) ⟩
  x * y + n × (x * y)   ≡⟨⟩
  suc n × (x * y)       ∎

-- (n ×_) associates with _*_

×-assoc-* : ∀ n x y → (n × x) * y ≈ n × (x * y)
×-assoc-* zero x y = zeroˡ y
×-assoc-* (suc n) x y = begin
  (suc n × x) * y       ≡⟨⟩
  (x + n × x) * y       ≈⟨ distribʳ _ _ _ ⟩
  x * y + (n × x) * y   ≈⟨ +-congˡ (×-assoc-* n _ _) ⟩
  x * y + n × (x * y)   ≡⟨⟩
  suc n × (x * y)       ∎

-- (_× x) is homomorphic with respect to _ℕ.*_/_*_ for idempotent x.

idem-×-homo-* : ∀ m n {x} → (_*_ IdempotentOn x) → (m × x) * (n × x) ≈ (m ℕ.* n) × x
idem-×-homo-* m n {x} idem = begin
  (m × x) * (n × x)   ≈⟨ ×-assoc-* m x (n × x) ⟩
  m × (x * (n × x))   ≈⟨ ×-congʳ m (×-comm-* n x x) ⟩
  m × (n × (x * x))   ≈⟨ ×-assocˡ _ m n ⟩
  (m ℕ.* n) × (x * x) ≈⟨ ×-congʳ (m ℕ.* n) idem ⟩
  (m ℕ.* n) × x       ∎

-- (_× 1#) is homomorphic with respect to _ℕ.*_/_*_.

×1-homo-* : ∀ m n → (m ℕ.* n) × 1# ≈ (m × 1#) * (n × 1#)
×1-homo-* m n = sym (idem-×-homo-* m n (*-identityʳ 1#))

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.1

1×-identityʳ = ×-homo-1
{-# WARNING_ON_USAGE 1×-identityʳ
"Warning: 1×-identityʳ was deprecated in v2.1.
Please use ×-homo-1 instead. "
#-}
