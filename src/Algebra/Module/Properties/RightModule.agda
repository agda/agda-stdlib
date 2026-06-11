------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of right modules.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles        using (Ring)
open import Algebra.Module.Bundles using (RightModule)
open import Level                  using (Level)

module Algebra.Module.Properties.RightModule
  {r ℓr m ℓm : Level}
  {ring  : Ring r ℓr}
  (mod   : RightModule ring m ℓm)
  where

open Ring        ring
open RightModule mod
open import Algebra.Properties.AbelianGroup +ᴹ-abelianGroup public
  using ()
  renaming (inverseˡ-unique to inverseˡ-uniqueᴹ
           ; inverseʳ-unique to inverseʳ-uniqueᴹ
           ; ⁻¹-involutive to -ᴹ-involutive)

open import Algebra.Properties.Ring ring

open import Relation.Binary.Reasoning.Setoid ≈ᴹ-setoid

-‿distrib-*ᵣ : ∀ m r → m *ᵣ (- r) ≈ᴹ -ᴹ (m *ᵣ r)
-‿distrib-*ᵣ m r = inverseʳ-uniqueᴹ (m *ᵣ r) (m *ᵣ - r) (begin
  m *ᵣ r +ᴹ m *ᵣ - r ≈⟨ *ᵣ-distribˡ m r (- r) ⟨
  m *ᵣ (r - r)       ≈⟨ *ᵣ-congˡ (-‿inverseʳ r) ⟩
  m *ᵣ 0#            ≈⟨ *ᵣ-zeroʳ m ⟩
  0ᴹ                 ∎)

-ᴹ‿distrib-*ᵣ : ∀ m r → (-ᴹ m) *ᵣ r ≈ᴹ -ᴹ (m *ᵣ r)
-ᴹ‿distrib-*ᵣ m r = inverseʳ-uniqueᴹ (m *ᵣ r) ((-ᴹ m) *ᵣ r) (begin
    m *ᵣ r +ᴹ (-ᴹ m) *ᵣ r ≈⟨ *ᵣ-distribʳ r m (-ᴹ m) ⟨
    (m +ᴹ -ᴹ m) *ᵣ r      ≈⟨ *ᵣ-congʳ (-ᴹ‿inverseʳ m) ⟩
    0ᴹ *ᵣ r               ≈⟨ *ᵣ-zeroˡ r ⟩
    0ᴹ                    ∎)

m*ᵣ-1#≈-ᴹm : ∀ m → m *ᵣ (- 1#) ≈ᴹ -ᴹ m
m*ᵣ-1#≈-ᴹm m = begin
  m *ᵣ (- 1#)  ≈⟨ -‿distrib-*ᵣ m 1# ⟩
  -ᴹ (m *ᵣ 1#) ≈⟨ -ᴹ‿cong (*ᵣ-identityʳ m) ⟩
  -ᴹ m         ∎

