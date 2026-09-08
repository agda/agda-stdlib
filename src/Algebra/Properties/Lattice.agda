------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `Algebra.Lattice.Properties.Lattice` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Lattice.Bundles
open import Relation.Binary.Core using (Rel)
open import Function.Base
open import Function.Bundles using (module Equivalence; _⇔_)
open import Data.Product.Base using (_,_; swap)

module Algebra.Properties.Lattice {l₁ l₂} (L : Lattice l₁ l₂) where

open import Algebra.Lattice.Properties.Lattice L public

{-# WARNING_ON_IMPORT
"Algebra.Properties.Lattice was deprecated in v2.0.
Use Algebra.Lattice.Properties.Lattice instead."
#-}
