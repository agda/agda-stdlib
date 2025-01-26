------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Semiring.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Semiring)

module Algebra.Properties.Semiring.Triviality
  {a ℓ} (R : Semiring a ℓ)
  where

import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open Semiring R renaming (Carrier to A)


------------------------------------------------------------------------
-- Re-export triviality definitions

open import Algebra.Definitions.RawSemiring rawSemiring public
  using (Trivial)

------------------------------------------------------------------------
-- Properties of Trivial

trivial⇒x≈0 : Trivial → ∀ x → x ≈ 0#
trivial⇒x≈0 trivial x = begin
  x        ≈⟨ *-identityˡ x ⟨
  1# * x   ≈⟨ *-congʳ trivial ⟩
  0# * x   ≈⟨ zeroˡ x ⟩
  0#       ∎
  where open ≈-Reasoning setoid

