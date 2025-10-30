------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of submodules
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Module.Bundles using (Module; RawModule)

module Algebra.Module.Construct.Sub.Module {c ℓ cm ℓm} {R : CommutativeRing c ℓ} (M : Module R cm ℓm) where

private
  module R = CommutativeRing R
  module M = Module M

open import Algebra.Construct.Sub.Group M.+ᴹ-group
open import Algebra.Module.Structures using (IsModule)
open import Algebra.Module.Morphism.Structures using (IsModuleMonomorphism)
import Algebra.Module.Morphism.ModuleMonomorphism as ModuleMonomorphism
open import Level using (suc; _⊔_)

record Submodule cm′ ℓm′ : Set (c ⊔ cm ⊔ ℓm ⊔ suc (cm′ ⊔ ℓm′)) where
  field
    domain : RawModule R.Carrier cm′ ℓm′

  private
    module N = RawModule domain

  field
    ι : N.Carrierᴹ → M.Carrierᴹ
    ι-monomorphism : IsModuleMonomorphism domain M.rawModule ι

  module ι = IsModuleMonomorphism ι-monomorphism

  isModule : IsModule R N._≈ᴹ_ N._+ᴹ_ N.0ᴹ N.-ᴹ_ N._*ₗ_ N._*ᵣ_
  isModule = ModuleMonomorphism.isModule ι-monomorphism R.isCommutativeRing M.isModule

  ⟨module⟩ : Module R _ _
  ⟨module⟩ = record { isModule = isModule }

  open Module ⟨module⟩ public hiding (isModule)

  subgroup : Subgroup cm′ ℓm′
  subgroup = record { ι-monomorphism = ι.+ᴹ-isGroupMonomorphism }
