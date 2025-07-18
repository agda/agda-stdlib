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
import Algebra.Consequences.Setoid setoid as Consequences
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Re-export binomial expansion

binomial-expansion : ∀ w x y z →
                     (w + x) * (y + z) ≈ w * y + w * z + x * y + x * z
binomial-expansion = Consequences.binomial-expansion +-cong +-assoc distrib

