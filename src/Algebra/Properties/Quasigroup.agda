------------------------------------------------------------------------
-- The Agda standard library
--
-- Shim for lemmas re-exported from Algebra.Properties.IsQuasigroup
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Quasigroup)

module Algebra.Properties.Quasigroup {q₁ q₂} (Q : Quasigroup q₁ q₂) where

open Quasigroup Q using (isQuasigroup)
open import Algebra.Properties.IsQuasigroup isQuasigroup public
