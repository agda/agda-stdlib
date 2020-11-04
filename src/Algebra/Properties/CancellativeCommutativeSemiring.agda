------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for CancellativeCommutativeSemiring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (CancellativeCommutativeSemiring)
import Algebra.GCD
import Algebra.Properties.Semigroup.Divisibility as SemigroupDiv
import Algebra.Properties.Semiring as SemiringProp
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_; flip)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; Symmetric; Setoid)
open import Relation.Unary using (Pred)

module Algebra.Properties.CancellativeCommutativeSemiring
  {α ℓ} (R : CancellativeCommutativeSemiring α ℓ)
  (open CancellativeCommutativeSemiring R)
  (0≉1 : 0# ≉ 1#)
  where

open SemigroupDiv *-semigroup using (_∣_; _∤_; ∣-trans)
open SemiringProp semiring using (∣nonzero⇒≉0)
open Algebra.GCD _≈_ 0# 1# _*_ using (IsIrreducible; IsPrime; Coprime; GCD)

private A = Carrier

0∤1 : 0# ∤ 1#
0∤1 (q , q*0≈1) = 0≉1 (trans (sym (zeroʳ q)) q*0≈1)

------------------------------------------------------------------------------
-- Properties of Irreducibilty, Coprime.

irreducible≉0 : ∀ {p} → IsIrreducible p → p ≉ 0#
irreducible≉0 (_ , chooseInvertible) p≈0 =
  let p≈0*0 = trans p≈0 (sym (zeroˡ 0#)) in
  case chooseInvertible p≈0*0 of λ
  { (inj₁ 0∣1) → 0∤1 0∣1
  ; (inj₂ 0∣1) → 0∤1 0∣1
  }

coprimeWithInvertible : ∀ {x} y → x ∣ 1# → Coprime x y
coprimeWithInvertible {x} y x∣1 z∣x _ = ∣-trans z∣x x∣1

------------------------------------------------------------------------------
-- Properties of GCD

module _ (a b : A) (struc : GCD a b)
  where
  open GCD struc

  nz⊎nz⇒≉0 : a ≉ 0# ⊎ b ≉ 0# → proper ≉ 0#
  nz⊎nz⇒≉0 (inj₁ a≉0) = ∣nonzero⇒≉0 divides₁ a≉0
  nz⊎nz⇒≉0 (inj₂ b≉0) = ∣nonzero⇒≉0 divides₂ b≉0

  quot₁ quot₂ : A
  quot₁ = proj₁ divides₁
  quot₂ = proj₁ divides₂

  quot₁*proper≈a : quot₁ * proper ≈ a
  quot₁*proper≈a = proj₂ divides₁

  quot₂*proper≈b : quot₂ * proper ≈ b
  quot₂*proper≈b = proj₂ divides₂

  quot₁∣a : quot₁ ∣ a
  quot₁∣a = (proper , proper*quot₁≈a)
    where
    proper*quot₁≈a = trans (*-comm proper quot₁) quot₁*proper≈a
