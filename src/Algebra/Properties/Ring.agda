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
import Algebra.Properties.Monoid as PM

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

------------------------------------------------------------------------
-- Reasoning combinators inherited from Monoid

open PM +-monoid using () renaming
  ( ε-unique to 0#-unique; ε-comm to 0#-comm
  ; elimʳ to +-elimʳ; introʳ to +-introʳ
  ; elimˡ to +-elimˡ; introˡ to +-introˡ
  ; introᶜ to +-introᶜ
  ; cancelʳ to +-cancel-invʳ; insertʳ to +-insertʳ
  ; cancelˡ to +-cancel-invˡ; insertˡ to +-insertˡ
  ; cancelᶜ to +-cancel-invᶜ; insertᶜ to +-insertᶜ) public

open PM *-monoid using () renaming
  ( ε-unique to 1#-unique; ε-comm to 1#-comm
  ; elimʳ to *-elimʳ; introʳ to *-introʳ
  ; elimˡ to *-elimˡ; introˡ to *-introˡ
  ; introᶜ to *-introᶜ
  ; cancelʳ to *-cancel-invʳ; insertʳ to *-insertʳ
  ; cancelˡ to *-cancel-invˡ; insertˡ to *-insertˡ
  ; cancelᶜ to *-cancel-invᶜ; insertᶜ to *-insertᶜ) public
