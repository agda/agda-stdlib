------------------------------------------------------------------------
-- The Agda standard library
--
-- Ideals of a ring
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Ring)

module Algebra.Construct.Sub.Ring.Ideal {c ℓ} (R : Ring c ℓ) where

open import Algebra.Module.Construct.Sub.Bimodule using (Subbimodule)
open import Algebra.Module.Construct.TensorUnit using (bimodule)
open import Level

------------------------------------------------------------------------
-- Definition
-- a (two sided) ideal is exactly a subbimodule of R considered as a bimodule over itself

record Ideal c′ ℓ′ : Set (c ⊔ ℓ ⊔ suc (c′ ⊔ ℓ′)) where
  field

    subbimodule : Subbimodule {R = R} bimodule c′ ℓ′

  open Subbimodule subbimodule public
