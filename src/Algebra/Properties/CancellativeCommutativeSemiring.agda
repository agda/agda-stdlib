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
  {a ℓ} (R : CancellativeCommutativeSemiring a ℓ)
  where

open CancellativeCommutativeSemiring R renaming (Carrier to A)

open Algebra.Primality _≈_ _*_ 0# 1# using (Irreducible; irredᶜ; Coprime)
open Algebra.GCD _≈_ _*_ using (GCD)

open SemigroupDiv *-semigroup public
--
-- Reexporting divisibility over Semigroup, Semiring
--
open SemiringDiv semiring public using (x∣y∧y≉0⇒x≉0)

0∤1 : 0# ≉ 1# → 0# ∤ 1#
0∤1 0≉1 (q , q*0≈1) = 0≉1 (trans (sym (zeroʳ q)) q*0≈1)

------------------------------------------------------------------------------
-- Properties of Irreducibilty, Coprime.

irreducible≉0 : 0# ≉ 1# → ∀ {p} → Irreducible p → p ≉ 0#
irreducible≉0 0≉1 (irredᶜ _ chooseInvertible) p≈0 =
  let p≈0*0 = trans p≈0 (sym (zeroˡ 0#)) in
  case chooseInvertible p≈0*0 of λ
  { (inj₁ 0∣1) → 0∤1 0≉1 0∣1
  ; (inj₂ 0∣1) → 0∤1 0≉1 0∣1
  }

coprimeWithInvertible : ∀ {x} y → x ∣ 1# → Coprime x y
coprimeWithInvertible {x} y x∣1 z∣x _ = ∣-trans z∣x x∣1

------------------------------------------------------------------------------
-- Properties of GCD

module _ (x y : A) (struc : GCD x y)
  where
  open GCD struc

  nz⊎nz⇒≉0 : x ≉ 0# ⊎ y ≉ 0# → value ≉ 0#
  nz⊎nz⇒≉0 (inj₁ x≉0) = x∣y∧y≉0⇒x≉0 divides₁ x≉0
  nz⊎nz⇒≉0 (inj₂ y≉0) = x∣y∧y≉0⇒x≉0 divides₂ y≉0

  quot₁∣x : quot₁ ∣ x
  quot₁∣x = (value , value*quot₁≈x)
    where
    value*quot₁≈x = trans (*-comm value quot₁) quot₁*value≈x

  quot₂∣y : quot₂ ∣ y
  quot₂∣y = (value , value*quot₂≈y)
    where
    value*quot₂≈y = trans (*-comm value quot₂) quot₂*value≈y
