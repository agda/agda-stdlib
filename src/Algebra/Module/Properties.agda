------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of modules.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra                using (Semiring)
open import Algebra.Module.Bundles using (LeftSemimodule)
open import Level                  using (Level)

module Algebra.Module.Properties
  {r ℓr m ℓm : Level} {semiring : Semiring r ℓr}
  (lsmod : LeftSemimodule semiring m ℓm)
  where

open import Relation.Nullary          using (¬_)
open import Relation.Nullary.Negation using (contraposition)

open LeftSemimodule lsmod
  using ( *ₗ-zeroˡ; *ₗ-zeroʳ; ≈ᴹ-setoid; *ₗ-congˡ; *ₗ-congʳ
        ; _*ₗ_; 0ᴹ; _≈ᴹ_; _≉ᴹ_)
  renaming (Carrierᴹ to M)

open Semiring semiring
  using (_≈_; _≉_; 0#) renaming (Carrier to R)

open import Relation.Binary.Reasoning.Setoid ≈ᴹ-setoid

s≈𝟘⇒s*v≈𝟘 : ∀ {s} {v} → s ≈ 0# → s *ₗ v ≈ᴹ 0ᴹ
s≈𝟘⇒s*v≈𝟘 {s} {v} s≈𝟘 = begin
  s  *ₗ v ≈⟨ *ₗ-congʳ s≈𝟘 ⟩
  0# *ₗ v ≈⟨ *ₗ-zeroˡ v ⟩
  0ᴹ      ∎

v≈𝟘⇒s*v≈𝟘 : ∀ {s} {v} → v ≈ᴹ 0ᴹ → s *ₗ v ≈ᴹ 0ᴹ
v≈𝟘⇒s*v≈𝟘 {s} {v} v≈𝟘 = begin
  s *ₗ v  ≈⟨ *ₗ-congˡ v≈𝟘 ⟩
  s *ₗ 0ᴹ ≈⟨ *ₗ-zeroʳ s ⟩
  0ᴹ      ∎

non-zeroˡ : ∀ {s} {v} → s *ₗ v ≉ᴹ 0ᴹ → s ≉ 0#
non-zeroˡ = contraposition s≈𝟘⇒s*v≈𝟘

non-zeroʳ : ∀ {s} {v} → s *ₗ v ≉ᴹ 0ᴹ → v ≉ᴹ 0ᴹ
non-zeroʳ = contraposition v≈𝟘⇒s*v≈𝟘
