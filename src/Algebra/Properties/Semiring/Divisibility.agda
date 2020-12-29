------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic items and theory for Semiring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semiring)
import Algebra.Properties.Monoid.Divisibility as MonoidDiv
open import Data.Product using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

module Algebra.Properties.Semiring.Divisibility {a ℓ} (R : Semiring a ℓ) where

open Semiring R

------------------------------------------------------------------------------
-- Re-exporting divisibility over monoids

open MonoidDiv *-monoid public renaming (ε∣_ to 1∣_)

------------------------------------------------------------------------------
-- Divisibility properties specific to Semiring.

_∣0 : ∀ x → x ∣ 0#
x ∣0 = 0# , zeroˡ x

0∣x⇒x≈0 : ∀ {x} → 0# ∣ x → x ≈ 0#
0∣x⇒x≈0 (q , q*0≈x) = trans (sym q*0≈x) (zeroʳ q)

x∣y∧y≉0⇒x≉0 : ∀ {x y} → x ∣ y → y ≉ 0# → x ≉ 0#
x∣y∧y≉0⇒x≉0 x∣y y≉0 x≈0 = y≉0 (0∣x⇒x≈0 (∣-respˡ x≈0 x∣y))

0∤1 : 0# ≉ 1# → 0# ∤ 1#
0∤1 0≉1 (q , q*0≈1) = 0≉1 (trans (sym (zeroʳ q)) q*0≈1)

------------------------------------------------------------------------------
-- Re-exporting definition of GCD

open import Algebra.Divisibility _≈_ _*_ public
  using (GCD)

------------------------------------------------------------------------------
-- Properties of GCD

module _ {x y} (struc : GCD x y) where
  open GCD struc

  x≉0⊎y≉0⇒gcd≉0 : x ≉ 0# ⊎ y ≉ 0# → value ≉ 0#
  x≉0⊎y≉0⇒gcd≉0 (inj₁ x≉0) = x∣y∧y≉0⇒x≉0 divides₁ x≉0
  x≉0⊎y≉0⇒gcd≉0 (inj₂ y≉0) = x∣y∧y≉0⇒x≉0 divides₂ y≉0
{-
  quot₁∣x : quot₁ ∣ x
  quot₁∣x = value , trans (*-comm value quot₁) quot₁*value≈x

  quot₂∣y : quot₂ ∣ y
  quot₂∣y = value , trans (*-comm value quot₂) quot₂*value≈y
-}
