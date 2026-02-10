------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Semirings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles
  using (Semiring)

module Algebra.Properties.Semiring
  {c ℓ} (semiring : Semiring c ℓ) where

open Semiring semiring

open import Algebra.Properties.SemiringWithoutOne semiringWithoutOne public
open import Algebra.Properties.Monoid *-monoid public
  using ()
  renaming
    ( ε-unique to 1#-unique
    ; ε-comm to 1#-comm

    ; elimʳ to *-elimʳ
    ; elimˡ to *-elimˡ
    ; introʳ to *-introʳ
    ; introˡ to *-introˡ
    ; introᶜ to *-introᶜ

    ; cancelʳ to *-cancelʳ
    ; cancelˡ to *-cancelˡ
    ; insertˡ to *-insertˡ
    ; insertʳ to *-insertʳ
    ; cancelᶜ to *-cancelᶜ
    ; insertᶜ to *-insertᶜ
    )
