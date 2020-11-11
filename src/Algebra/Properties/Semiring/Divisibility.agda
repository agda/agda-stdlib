------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic items and theory for Semiring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semiring)
import Algebra.Properties.Monoid.Divisibility as MonoidDiv
open import Data.Product using (_,_)

module Algebra.Properties.Semiring.Divisibility {r₁ r₂} (R : Semiring r₁ r₂) where

open Semiring R
open import Algebra.Divisibility _≈_ _*_ using (∣-max)
open MonoidDiv *-monoid public

------------------------------------------------------------------------------
-- Divisibility properties specific to Semiring.

1∣ : ∀ x → 1# ∣ x
1∣ = ε∣_

∣0 : ∀ x → x ∣ 0#
∣0 x = ∣-max zeroˡ x

0∣x⇒x≈0 : ∀ {x} → 0# ∣ x → x ≈ 0#
0∣x⇒x≈0 (q , q*0≈x) = trans (sym q*0≈x) (zeroʳ q)

∣nonzero⇒≉0 : ∀ {x y} → x ∣ y → y ≉ 0# → x ≉ 0#
∣nonzero⇒≉0 x∣y y≉0 x≈0 = y≉0 (0∣x⇒x≈0 (∣-respˡ x≈0 x∣y))
