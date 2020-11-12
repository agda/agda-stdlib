------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic items and theory for Semiring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semiring)
import Algebra.Properties.Monoid.Divisibility as MonoidDiv
open import Data.Product using (_,_)

module Algebra.Properties.Semiring.Divisibility {α ℓ} (R : Semiring α ℓ) where

open Semiring R

-- Re-exporting contents of divisibility over monoids
--
open MonoidDiv *-monoid public renaming (ε∣_ to 1∣_)

------------------------------------------------------------------------------
-- Divisibility properties specific to Semiring.

_∣0 : ∀ x → x ∣ 0#
x ∣0 = 0# , zeroˡ x

0∣x⇒x≈0 : ∀ {x} → 0# ∣ x → x ≈ 0#
0∣x⇒x≈0 (q , q*0≈x) = trans (sym q*0≈x) (zeroʳ q)

∣nonzero⇒≉0 : ∀ {x y} → x ∣ y → y ≉ 0# → x ≉ 0#
∣nonzero⇒≉0 x∣y y≉0 x≈0 = y≉0 (0∣x⇒x≈0 (∣-respˡ x≈0 x∣y))
