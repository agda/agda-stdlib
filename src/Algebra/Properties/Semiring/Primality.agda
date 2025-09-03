------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Coprimality and Irreducibility for Semiring.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Semiring)

module Algebra.Properties.Semiring.Primality
  {a ℓ} (R : Semiring a ℓ)
  where

open import Data.Sum.Base using (reduce)
open import Function.Base using (flip)
open import Relation.Binary.Definitions using (Symmetric)

open Semiring R renaming (Carrier to A)
open import Algebra.Properties.Semiring.Divisibility R
  using (_∣_; ∣-trans; 0∤1)

private
  variable
    x : A

------------------------------------------------------------------------
-- Re-export primality definitions

open import Algebra.Definitions.RawSemiring rawSemiring public
  using (Coprime; Prime; mkPrime; Irreducible; mkIrred)

------------------------------------------------------------------------
-- Properties of Coprime

Coprime-sym : Symmetric Coprime
Coprime-sym coprime = flip coprime

∣1⇒Coprime : ∀ y → x ∣ 1# → Coprime x y
∣1⇒Coprime _ x∣1 z∣x _ = ∣-trans z∣x x∣1

------------------------------------------------------------------------
-- Properties of Irreducible

Irreducible⇒≉0 : 0# ≉ 1# → ∀ {p} → Irreducible p → p ≉ 0#
Irreducible⇒≉0 0≉1 (mkIrred _ chooseInvertible) p≈0 =
  0∤1 0≉1 (reduce (chooseInvertible (trans p≈0 (sym (zeroˡ 0#)))))
