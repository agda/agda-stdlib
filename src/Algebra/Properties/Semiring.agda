------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic items and theory for Semiring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semiring)
import Algebra.Properties.Monoid
open import Data.Product using (_,_)
open import Relation.Binary using (Setoid)

module Algebra.Properties.Semiring {r₁ r₂} (R : Semiring r₁ r₂) where

open Semiring R
open Setoid setoid using (_≉_)
open Algebra.Properties.Monoid *-monoid using (_∣_; ∣-respˡ; ε∣)

------------------------------------------------------------------------------
-- Divisibility lemmata specific for Semiring.
------------------------------------------------------------------------------

1∣ : ∀ x → 1# ∣ x
1∣ = ε∣

∣0 : ∀ x → x ∣ 0#
∣0 x = (0# , sym (zeroˡ x))

0∣x⇒x≈0 : ∀ {x} → 0# ∣ x → x ≈ 0#
0∣x⇒x≈0 (q , x≈q*0) = trans x≈q*0 (zeroʳ q)

∣nonzero⇒≉0 : ∀ {x y} → x ∣ y → y ≉ 0# → x ≉ 0#
∣nonzero⇒≉0 x∣y y≉0 x≈0 = y≉0 (0∣x⇒x≈0 0∣y)
 where
 0∣y = ∣-respˡ x≈0 x∣y
