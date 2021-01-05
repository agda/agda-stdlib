------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for CancellativeCommutativeSemiring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semiring)
import Algebra.Primality
import Algebra.Properties.Semigroup.Divisibility as SemigroupDiv
import Algebra.Properties.Semiring.Divisibility as SemiringDiv
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; reduce)
open import Function using (case_of_; flip)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; Symmetric; Setoid)
open import Relation.Unary using (Pred)

module Algebra.Properties.Semiring.Primality
  {a ℓ} (R : Semiring a ℓ)
  where

open Semiring R renaming (Carrier to A)
open SemiringDiv R

------------------------------------------------------------------------
-- Re-export primality definitions

open Algebra.Primality _≈_ _*_ 0# 1# public

------------------------------------------------------------------------
-- Properties of Irreducible

Irreducible⇒≉0 : 0# ≉ 1# → ∀ {p} → Irreducible p → p ≉ 0#
Irreducible⇒≉0 0≉1 (mkIrred _ chooseInvertible) p≈0 =
  0∤1 0≉1 (reduce (chooseInvertible (trans p≈0 (sym (zeroˡ 0#)))))

------------------------------------------------------------------------
-- Properties of Coprime

Coprime-sym : Symmetric Coprime
Coprime-sym coprime = flip coprime

∣1⇒Coprime : ∀ {x} y → x ∣ 1# → Coprime x y
∣1⇒Coprime {x} y x∣1 z∣x _ = ∣-trans z∣x x∣1
