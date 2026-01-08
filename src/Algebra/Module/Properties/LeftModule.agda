------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of left modules.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles        using (Ring)
open import Algebra.Module.Bundles using (LeftModule)
open import Level                  using (Level)

module Algebra.Module.Properties.LeftModule
  {r ℓr m ℓm : Level}
  {ring  : Ring r ℓr}
  (mod   : LeftModule ring m ℓm)
  where

open Ring       ring
open LeftModule mod
open import Algebra.Properties.AbelianGroup +ᴹ-abelianGroup public
  using ()
  renaming (inverseˡ-unique to inverseˡ-uniqueᴹ
           ; inverseʳ-unique to inverseʳ-uniqueᴹ
           ; ⁻¹-involutive to -ᴹ-involutive)

open import Algebra.Properties.Ring ring

open import Relation.Binary.Reasoning.Setoid ≈ᴹ-setoid

-‿distrib-*ₗ : ∀ r m → - r *ₗ m ≈ᴹ -ᴹ (r *ₗ m)
-‿distrib-*ₗ r m = uniqueʳ‿-ᴹ (r *ₗ m) (- r *ₗ m) (begin
  r *ₗ m +ᴹ - r *ₗ m ≈⟨ *ₗ-distribʳ m r (- r) ⟨
  (r - r) *ₗ m       ≈⟨ *ₗ-congʳ (-‿inverseʳ r) ⟩
  0# *ₗ m            ≈⟨ *ₗ-zeroˡ m ⟩
  0ᴹ                 ∎)

-ᴹ‿distrib-*ₗ : ∀ r m → r *ₗ (-ᴹ m) ≈ᴹ -ᴹ (r *ₗ m)
-ᴹ‿distrib-*ₗ r m = uniqueʳ‿-ᴹ (r *ₗ m) (r *ₗ (-ᴹ m))
  (begin
    r *ₗ m +ᴹ r *ₗ (-ᴹ m) ≈⟨ *ₗ-distribˡ r m (-ᴹ m) ⟨
    r *ₗ (m +ᴹ (-ᴹ m))    ≈⟨ *ₗ-congˡ (-ᴹ‿inverseʳ m) ⟩
    r *ₗ 0ᴹ               ≈⟨ *ₗ-zeroʳ r ⟩
    0ᴹ                    ∎)

-1#*m≈-ᴹm : ∀ m → - 1# *ₗ m ≈ᴹ -ᴹ m
-1#*m≈-ᴹm m = begin
  - 1# *ₗ m    ≈⟨ -‿distrib-*ₗ 1# m ⟩
  -ᴹ (1# *ₗ m) ≈⟨ -ᴹ‿cong (*ₗ-identityˡ m) ⟩
  -ᴹ m         ∎
