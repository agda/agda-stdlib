------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of scaling.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra                using (Semiring)
open import Algebra.Module.Bundles using (LeftSemimodule)
open import Level                  using (Level)

module Algebra.Module.Properties
  {r ℓr m ℓm : Level} {semiring : Semiring r ℓr}
  (lsmod : LeftSemimodule semiring m ℓm)
  where

open import Relation.Nullary       using (¬_)

open LeftSemimodule lsmod
  using (*ₗ-zeroˡ; *ₗ-zeroʳ; ≈ᴹ-setoid; _≈ᴹ_; *ₗ-congˡ; *ₗ-congʳ)
  renaming
  ( Carrierᴹ to M
  ; _*ₗ_     to _·_
  ; 0ᴹ       to 𝟘
  )
infix 3 _≉ᴹ_
_≉ᴹ_ : M → M → Set ℓm
x ≉ᴹ y = ¬ (x ≈ᴹ y)

open Semiring semiring
  using (_≉_) renaming
  ( Carrier to R
  ; 0#      to 0ᴿ
  )

open import Relation.Binary.Reasoning.Setoid ≈ᴹ-setoid

non-zeroˡ : {s : R} {v : M} → s · v ≉ᴹ 𝟘 → s ≉ 0ᴿ
non-zeroˡ {s = s} {v = v} s·v≉𝟘 = λ { s≈0ᴿ →
  let s·v≈𝟘 : s  · v ≈ᴹ 𝟘
      s·v≈𝟘 = begin
              s  · v ≈⟨ *ₗ-congʳ s≈0ᴿ ⟩
              0ᴿ · v ≈⟨ *ₗ-zeroˡ v ⟩
              𝟘 ∎
   in s·v≉𝟘 s·v≈𝟘
  }

non-zeroʳ : {s : R} {v : M} → s · v ≉ᴹ 𝟘 → v ≉ᴹ 𝟘
non-zeroʳ {s = s} {v = v} s·v≉𝟘 = λ { v≈𝟘 →
  let s·v≈𝟘 : s · v ≈ᴹ 𝟘
      s·v≈𝟘 = begin
              s · v ≈⟨ *ₗ-congˡ v≈𝟘 ⟩
              s · 𝟘 ≈⟨ *ₗ-zeroʳ s ⟩
              𝟘 ∎
   in s·v≉𝟘 s·v≈𝟘
  }
