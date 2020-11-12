------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for CancellativeCommutativeSemiring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (CancellativeCommutativeSemiring)
import Algebra.GCD
import Algebra.Primality
import Algebra.Properties.Semigroup.Divisibility as SemigroupDiv
import Algebra.Properties.Semiring.Divisibility as SemiringDiv
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_; flip)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; Symmetric; Setoid)
open import Relation.Unary using (Pred)

module Algebra.Properties.CancellativeCommutativeSemiring
  {α ℓ} (R : CancellativeCommutativeSemiring α ℓ)
  where

open CancellativeCommutativeSemiring R renaming (Carrier to A)

open SemigroupDiv *-semigroup using (_∣_; _∤_; ∣-trans)
--
-- Reexporting Divisibility over Semigroup, Semiring
--
open SemiringDiv semiring using (∣nonzero⇒≉0)

open Algebra.Primality _≈_ _*_ 0# 1# using (Irreducible; Coprime)
open Algebra.GCD _≈_ _*_ using (GCD)

0∤1 : 0# ≉ 1# → 0# ∤ 1#
0∤1 0≉1 (q , q*0≈1) = 0≉1 (trans (sym (zeroʳ q)) q*0≈1)

------------------------------------------------------------------------------
-- Properties of Irreducibilty, Coprime.

irreducible≉0 : 0# ≉ 1# → ∀ {x} → Irreducible x → x ≉ 0#
irreducible≉0 0≉1 (_ , chooseInvertible) x≈0 =
  let x≈0*0 = trans x≈0 (sym (zeroˡ 0#)) in
  case chooseInvertible x≈0*0 of λ
  { (inj₁ 0∣1) → 0∤1 0≉1 0∣1
  ; (inj₂ 0∣1) → 0∤1 0≉1 0∣1
  }

coprimeWithInvertible : ∀ {x} y → x ∣ 1# → Coprime x y
coprimeWithInvertible {x} y x∣1 z∣x _ = ∣-trans z∣x x∣1

------------------------------------------------------------------------------
-- Properties of GCD

module _ (a b : A) (struc : GCD a b)
  where
  open GCD struc

  nz⊎nz⇒≉0 : a ≉ 0# ⊎ b ≉ 0# → value ≉ 0#
  nz⊎nz⇒≉0 (inj₁ a≉0) = ∣nonzero⇒≉0 divides₁ a≉0
  nz⊎nz⇒≉0 (inj₂ b≉0) = ∣nonzero⇒≉0 divides₂ b≉0

  quot₁∣a : quot₁ ∣ a
  quot₁∣a = (value , value*quot₁≈a)
    where
    value*quot₁≈a = trans (*-comm value quot₁) quot₁*value≈arg1

  quot₂∣b : quot₂ ∣ b
  quot₂∣b = (value , value*quot₂≈b)
    where
    value*quot₂≈b = trans (*-comm value quot₂) quot₂*value≈arg2
