------------------------------------------------------------------------
-- The Agda standard library
--
-- The kernel of a ring homomorphism is an ideal
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles
open import Algebra.Morphism.Structures

module Algebra.Ideal.Construct.Kernel
  {c ℓ c′ ℓ′}
  {R : Ring c ℓ}
  {S : Ring c′ ℓ′}
  (ρ : Ring.Carrier R → Ring.Carrier S)
  (homomorphism : IsRingHomomorphism (Ring.rawRing R) (Ring.rawRing S) ρ)
  where

private
  module R = Ring R
  module S = Ring S
  module ρ = IsRingHomomorphism homomorphism

open import Algebra.NormalSubgroup.Construct.Kernel {G = R.+-group} {H = S.+-group} ρ ρ.+-isGroupHomomorphism public
  renaming (_∙ₖ_ to _+ₖ_; εₖ to 0#ₖ; _⁻¹ₖ to -ₖ_)

open import Algebra.Ideal R
open import Algebra.Module.Bundles.Raw
open import Function.Base
open import Level
open import Relation.Binary.Reasoning.Setoid S.setoid


_*ₗₖ_ : R.Carrier → Kernel → Kernel
r *ₗₖ x = record
  { element = r R.* X.element
  ; inKernel = begin
    ρ (r R.* X.element) ≈⟨ ρ.*-homo r X.element ⟩
    ρ r S.* ρ X.element ≈⟨ S.*-congˡ X.inKernel ⟩
    ρ r S.* S.0#        ≈⟨ S.zeroʳ (ρ r) ⟩
    S.0#                ∎
  }
  where module X = Kernel x

_*ᵣₖ_ : Kernel → R.Carrier → Kernel
x *ᵣₖ r = record
  { element = X.element R.* r
  ; inKernel = begin
    ρ (X.element R.* r) ≈⟨ ρ.*-homo X.element r ⟩
    ρ X.element S.* ρ r ≈⟨ S.*-congʳ X.inKernel ⟩
    S.0# S.* ρ r        ≈⟨ S.zeroˡ (ρ r) ⟩
    S.0#                ∎
  }
  where module X = Kernel x

Kernel-rawModule : RawModule R.Carrier (c ⊔ ℓ′) ℓ
Kernel-rawModule = record
  { Carrierᴹ = Kernel
  ; _≈ᴹ_ = R._≈_ on Kernel.element
  ; _+ᴹ_ = _+ₖ_
  ; _*ₗ_ = _*ₗₖ_
  ; _*ᵣ_ = _*ᵣₖ_
  ; 0ᴹ = 0#ₖ
  ; -ᴹ_ = -ₖ_
  }
  where open RawGroup Kernel-rawGroup

kernelIdeal : Ideal (c ⊔ ℓ′) ℓ
kernelIdeal = record
  { I = Kernel-rawModule
  ; ι = Kernel.element
  ; ι-monomorphism = record
    { isModuleHomomorphism = record
      { isBimoduleHomomorphism = record
        { +ᴹ-isGroupHomomorphism = IsGroupMonomorphism.isGroupHomomorphism element-isGroupMonomorphism
        ; *ₗ-homo = λ _ _ → R.refl
        ; *ᵣ-homo = λ _ _ → R.refl
        }
      }
    ; injective = λ p → p
    }
  }
