------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of a monomorphism between bimodules
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Module.Bundles.Raw
open import Algebra.Module.Morphism.Structures

module Algebra.Module.Morphism.BimoduleMonomorphism
  {r s a b ℓ₁ ℓ₂} {R : Set r} {S : Set s} {M : RawBimodule R S a ℓ₁} {N : RawBimodule R S b ℓ₂} {⟦_⟧}
  (isBimoduleMonomorphism : IsBimoduleMonomorphism M N ⟦_⟧)
  where

open IsBimoduleMonomorphism isBimoduleMonomorphism
private
  module M = RawBimodule M
  module N = RawBimodule N

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
open import Algebra.Module.Morphism.BisemimoduleMonomorphism isBisemimoduleMonomorphism public

------------------------------------------------------------------------
-- Structures

module _
  {ℓr} {_≈r_ : Rel R ℓr} {_+r_ _*r_ -r_ 0r 1r}
  {ℓs} {_≈s_ : Rel S ℓs} {_+s_ _*s_ -s_ 0s 1s}
  (R-isRing : IsRing _≈r_ _+r_ _*r_ -r_ 0r 1r)
  (S-isRing : IsRing _≈s_ _+s_ _*s_ -s_ 0s 1s)
  where

  private
    R-ring : Ring _ _
    R-ring = record { isRing = R-isRing }

    S-ring : Ring _ _
    S-ring = record { isRing = S-isRing }

    module R = IsRing R-isRing
    module S = IsRing S-isRing

  isBimodule
    : IsBimodule R-ring S-ring N._≈ᴹ_ N._+ᴹ_ N.0ᴹ N.-ᴹ_ N._*ₗ_ N._*ᵣ_
    → IsBimodule R-ring S-ring M._≈ᴹ_ M._+ᴹ_ M.0ᴹ M.-ᴹ_ M._*ₗ_ M._*ᵣ_
  isBimodule isBimodule = record
    { isBisemimodule = isBisemimodule R.isSemiring S.isSemiring NN.isBisemimodule
    ; -ᴹ‿cong = -ᴹ‿cong NN.+ᴹ-isMagma NN.-ᴹ‿cong
    ; -ᴹ‿inverse = -ᴹ‿inverse NN.+ᴹ-isMagma NN.-ᴹ‿inverse
    }
    where
      module NN = IsBimodule isBimodule

