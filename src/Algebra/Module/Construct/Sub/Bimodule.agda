------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of submodules
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Ring)
open import Algebra.Module.Bundles using (Bimodule; RawBimodule)

module Algebra.Module.Construct.Sub.Bimodule {cr ℓr cs ℓs cm ℓm} {R : Ring cr ℓr} {S : Ring cs ℓs}  (M : Bimodule R S cm ℓm) where

private
  module R = Ring R
  module S = Ring S
  module M = Bimodule M

open import Algebra.Construct.Sub.Group M.+ᴹ-group
open import Algebra.Module.Structures using (IsBimodule)
open import Algebra.Module.Morphism.Structures using (IsBimoduleMonomorphism)
import Algebra.Module.Morphism.BimoduleMonomorphism as BimoduleMonomorphism
open import Level using (suc; _⊔_)

record Subbimodule cm′ ℓm′ : Set (cr ⊔ cs ⊔ cm ⊔ ℓm ⊔ suc (cm′ ⊔ ℓm′)) where
  field
    domain : RawBimodule R.Carrier S.Carrier cm′ ℓm′

  private
    module N = RawBimodule domain

  field
    ι : N.Carrierᴹ → M.Carrierᴹ
    ι-monomorphism : IsBimoduleMonomorphism domain M.rawBimodule ι

  module ι = IsBimoduleMonomorphism ι-monomorphism

  isBimodule : IsBimodule R S N._≈ᴹ_ N._+ᴹ_ N.0ᴹ N.-ᴹ_ N._*ₗ_ N._*ᵣ_
  isBimodule = BimoduleMonomorphism.isBimodule ι-monomorphism R.isRing S.isRing M.isBimodule

  bimodule : Bimodule R S _ _
  bimodule = record { isBimodule = isBimodule }

  open Bimodule bimodule public hiding (isBimodule)

  subgroup : Subgroup cm′ ℓm′
  subgroup = record { ι-monomorphism = ι.+ᴹ-isGroupMonomorphism }
