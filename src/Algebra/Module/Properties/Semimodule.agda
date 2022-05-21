------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of semimodules.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra                using (CommutativeSemiring)
open import Algebra.Module.Bundles using (Semimodule)
open import Level                  using (Level)

module Algebra.Module.Properties.Semimodule
  {r ℓr m ℓm : Level}
  {semiring  : CommutativeSemiring r ℓr}
  (semimod   : Semimodule semiring m ℓm)
  where

open CommutativeSemiring semiring
open Semimodule          semimod
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Binary.Reasoning.Setoid ≈ᴹ-setoid

s≈0⇒s*v≈0 : ∀ {s} {v} → s ≈ 0# → s *ₗ v ≈ᴹ 0ᴹ
s≈0⇒s*v≈0 {s} {v} s≈0 = begin
  s  *ₗ v ≈⟨ *ₗ-congʳ s≈0 ⟩
  0# *ₗ v ≈⟨ *ₗ-zeroˡ v ⟩
  0ᴹ      ∎

v≈0⇒s*v≈0 : ∀ {s} {v} → v ≈ᴹ 0ᴹ → s *ₗ v ≈ᴹ 0ᴹ
v≈0⇒s*v≈0 {s} {v} v≈0 = begin
  s *ₗ v  ≈⟨ *ₗ-congˡ v≈0 ⟩
  s *ₗ 0ᴹ ≈⟨ *ₗ-zeroʳ s ⟩
  0ᴹ      ∎

s*v≉0⇒s≉0 : ∀ {s} {v} → s *ₗ v ≉ᴹ 0ᴹ → s ≉ 0#
s*v≉0⇒s≉0 = contraposition s≈0⇒s*v≈0

s*v≉0⇒v≉0 : ∀ {s} {v} → s *ₗ v ≉ᴹ 0ᴹ → v ≉ᴹ 0ᴹ
s*v≉0⇒v≉0 = contraposition v≈0⇒s*v≈0
