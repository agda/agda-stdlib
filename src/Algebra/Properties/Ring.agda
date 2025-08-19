------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Rings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra using (Ring)

module Algebra.Properties.Ring {c ℓ} (ring : Ring c ℓ) where

open Ring ring
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Export properties of rings without a 1#.

open import Algebra.Properties.RingWithoutOne ringWithoutOne public

------------------------------------------------------------------------
-- Extra properties of 1#

-1*x≈-x : ∀ x → - 1# * x ≈ - x
-1*x≈-x x = begin
  - 1# * x    ≈⟨ -‿distribˡ-* 1# x ⟨
  - (1# * x)  ≈⟨ -‿cong ( *-identityˡ x ) ⟩
  - x         ∎
