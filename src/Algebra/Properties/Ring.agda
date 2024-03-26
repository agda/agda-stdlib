------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Rings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra using (Ring)

module Algebra.Properties.Ring {r₁ r₂} (R : Ring r₁ r₂) where

open Ring R

import Algebra.Properties.RingWithoutOne as RingWithoutOneProperties
open import Function.Base using (_$_)
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Definitions _≈_

------------------------------------------------------------------------
-- Export properties of rings without a 1#.

open RingWithoutOneProperties ringWithoutOne public

------------------------------------------------------------------------
-- Extra properties of 1#

-1*x≈-x : ∀ x → - 1# * x ≈ - x
-1*x≈-x x = begin
  - 1# * x    ≈⟨ -‿distribˡ-* 1# x ⟨
  - (1# * x)  ≈⟨ -‿cong ( *-identityˡ x ) ⟩
  - x         ∎
