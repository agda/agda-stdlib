------------------------------------------------------------------------
-- The Agda standard library
--
-- Ideals of a ring
--
-- Based on Nathan van Doorn (Taneb)'s original PR
-- https://github.com/agda/agda-stdlib/pull/2855
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Ring)

-- As with `Algebra.Construct.Sub.Group.Normal`, this module
-- relocates Taneb's original `Algebra.Ideal`
-- to a level one *below* that of `Algebra.Construct.Sub.Ring`,
-- notwithstanding that we have yet to define `Sub.XRing`s...

module Algebra.Construct.Sub.Ring.Ideal {c ℓ} (R : Ring c ℓ) where

open import Algebra.Module.Construct.Sub.Bimodule using (Subbimodule)
open import Algebra.Module.Construct.TensorUnit using (bimodule)
open import Level using (suc; _⊔_)

------------------------------------------------------------------------
-- Definition
--
-- A (two sided) ideal is exactly a sub-bimodule of R, considered as
-- a bimodule (the `TensorUnit` for that category) over itself.

record Ideal c′ ℓ′ : Set (c ⊔ ℓ ⊔ suc (c′ ⊔ ℓ′)) where
  field
    subbimodule : Subbimodule {R = R} bimodule c′ ℓ′

-- The definition of `Subbimodule` now exports the `normalSubgroup`
-- and `abelianGroup` definitions, so that a `Ring` modulo an `Ideal`
-- already has direct access to the underlying quotient `(Abelian)Group`
-- structure on the additive group of the ring.

  open Subbimodule subbimodule public
