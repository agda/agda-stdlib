------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility over semirings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Semiring)

module Algebra.Properties.Semiring.Divisibility
  {a ℓ} (R : Semiring a ℓ) where

open Semiring R

------------------------------------------------------------------------
-- Re-exporting divisibility over monoids

open import Algebra.Properties.Monoid.Divisibility *-monoid public
  renaming (ε∣_ to 1∣_)

------------------------------------------------------------------------
-- Divisibility properties specific to semirings.

infixr 8 _∣0

_∣0 : ∀ x → x ∣ 0#
x ∣0 = 0# , zeroˡ x

0∣x⇒x≈0 : ∀ {x} → 0# ∣ x → x ≈ 0#
0∣x⇒x≈0 (q , q*0≈x) = trans (sym q*0≈x) (zeroʳ q)

x∣y∧y≉0⇒x≉0 : ∀ {x y} → x ∣ y → y ≉ 0# → x ≉ 0#
x∣y∧y≉0⇒x≉0 x∣y y≉0 x≈0 = y≉0 (0∣x⇒x≈0 (∣-respˡ x≈0 x∣y))

0∤1 : 0# ≉ 1# → 0# ∤ 1#
0∤1 0≉1 0∣1 = 0≉1 (sym (0∣x⇒x≈0 0∣1))
