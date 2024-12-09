------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a monomorphism between left modules
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Module.Bundles.Raw
open import Algebra.Module.Morphism.Structures

module Algebra.Module.Morphism.LeftModuleMonomorphism
  {r a b ℓ₁ ℓ₂} {R : Set r} {M : RawLeftModule R a ℓ₁} {N : RawLeftModule R b ℓ₂} {⟦_⟧}
  (isLeftModuleMonomorphism : IsLeftModuleMonomorphism M N ⟦_⟧)
  where

open IsLeftModuleMonomorphism isLeftModuleMonomorphism
private
  module M = RawLeftModule M
  module N = RawLeftModule N

open import Algebra.Bundles
open import Algebra.Core
open import Algebra.Module.Structures
open import Algebra.Structures
open import Relation.Binary.Core

------------------------------------------------------------------------
-- Re-exports

open import Algebra.Morphism.GroupMonomorphism +ᴹ-isGroupMonomorphism public
  using () renaming
    ( inverseˡ to -ᴹ‿inverseˡ
    ; inverseʳ to -ᴹ‿inverseʳ
    ; inverse to -ᴹ‿inverse
    ; ⁻¹-cong to -ᴹ‿cong
    ; ⁻¹-distrib-∙ to -ᴹ‿distrib-+ᴹ
    ; isGroup to +ᴹ-isGroup
    ; isAbelianGroup to +ᴹ-isAbelianGroup
    )
open import Algebra.Module.Morphism.LeftSemimoduleMonomorphism isLeftSemimoduleMonomorphism public

------------------------------------------------------------------------
-- Structures

module _ {ℓr} {_≈_ : Rel R ℓr} {_+_ _*_ -_ 0# 1#} (R-isRing : IsRing _≈_ _+_ _*_ -_ 0# 1#) where

  private
    R-ring : Ring _ _
    R-ring = record { isRing = R-isRing }
  open IsRing R-isRing

  isLeftModule
    : IsLeftModule R-ring N._≈ᴹ_ N._+ᴹ_ N.0ᴹ N.-ᴹ_ N._*ₗ_
    → IsLeftModule R-ring M._≈ᴹ_ M._+ᴹ_ M.0ᴹ M.-ᴹ_ M._*ₗ_
  isLeftModule isLeftModule = record
    { isLeftSemimodule = isLeftSemimodule isSemiring NN.isLeftSemimodule
    ; -ᴹ‿cong = -ᴹ‿cong NN.+ᴹ-isMagma NN.-ᴹ‿cong
    ; -ᴹ‿inverse = -ᴹ‿inverse NN.+ᴹ-isMagma NN.-ᴹ‿inverse
    }
    where
      module NN = IsLeftModule isLeftModule
