------------------------------------------------------------------------
-- The Agda standard library
--
-- Ideals of a ring
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Ring)

module Algebra.Ideal {c ℓ} (R : Ring c ℓ) where

open Ring R using (+-group; +-comm)

open import Algebra.Module.Construct.Sub.Bimodule using (Subbimodule)
import Algebra.Module.Construct.TensorUnit as TU
open import Algebra.NormalSubgroup (+-group)
open import Level

record Ideal c′ ℓ′ : Set (c ⊔ ℓ ⊔ suc (c′ ⊔ ℓ′)) where
  field
    -- a (two sided) ideal is exactly a subbimodule of R considered as a bimodule over itself
    subbimodule : Subbimodule (TU.bimodule {R = R}) c′ ℓ′

  open Subbimodule subbimodule public

  normalSubgroup : NormalSubgroup c′ ℓ′
  normalSubgroup = record
    { isNormal = abelian⇒subgroup-normal +-comm subgroup
    }
