------------------------------------------------------------------------
-- The kernel of a group homomorphism is a normal subgroup
--
-- The Agda standard library
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles
open import Algebra.Morphism.Structures

module Algebra.NormalSubgroup.Construct.Kernel
  {c ℓ c′ ℓ′}
  {G : Group c ℓ}
  {H : Group c′ ℓ′}
  (ρ : Group.Carrier G → Group.Carrier H)
  (homomorphism : IsGroupHomomorphism (Group.rawGroup G) (Group.rawGroup H) ρ)
  where

open import Algebra.NormalSubgroup
open import Algebra.Properties.Group
open import Data.Product.Base
open import Function.Base
open import Level
open import Relation.Binary.Reasoning.MultiSetoid

private
  module G = Group G
  module H = Group H
  module ρ = IsGroupHomomorphism homomorphism

record Kernel : Set (c ⊔ ℓ′) where
  field
    element : G.Carrier
    inKernel : ρ element H.≈ H.ε

_∙ₖ_ : Kernel → Kernel → Kernel
x ∙ₖ y = record
  { element = X.element G.∙ Y.element
  ; inKernel = begin⟨ H.setoid ⟩
    ρ (X.element G.∙ Y.element) ≈⟨ ρ.homo X.element Y.element ⟩
    ρ X.element H.∙ ρ Y.element ≈⟨ H.∙-cong X.inKernel Y.inKernel ⟩
    H.ε H.∙ H.ε                 ≈⟨ H.identityˡ H.ε ⟩
    H.ε                         ∎
  }
  where
    module X = Kernel x
    module Y = Kernel y

εₖ : Kernel
εₖ = record
   { element = G.ε
   ; inKernel = ρ.ε-homo
   }
     
_⁻¹ₖ : Kernel → Kernel
x ⁻¹ₖ = record
  { element = X.element G.⁻¹
  ; inKernel = begin⟨ H.setoid ⟩
    ρ (X.element G.⁻¹) ≈⟨ ρ.⁻¹-homo X.element ⟩
    ρ X.element H.⁻¹   ≈⟨ H.⁻¹-cong X.inKernel ⟩
    H.ε H.⁻¹           ≈⟨ ε⁻¹≈ε H ⟩
    H.ε                ∎
  }
  where
    module X = Kernel x

Kernel-rawGroup : RawGroup (c ⊔ ℓ′) ℓ
Kernel-rawGroup = record
  { Carrier = Kernel
  ; _≈_ = G._≈_ on Kernel.element
  ; _∙_ = _∙ₖ_
  ; ε = εₖ
  ; _⁻¹ = _⁻¹ₖ
  }

element-isGroupMonomorphism : IsGroupMonomorphism Kernel-rawGroup G.rawGroup Kernel.element
element-isGroupMonomorphism = record
  { isGroupHomomorphism = record
    { isMonoidHomomorphism = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record
          { cong = λ p → p
          }
        ; homo = λ x y → G.refl
        }
      ; ε-homo = G.refl
      }
    ; ⁻¹-homo = λ x → G.refl
    }
  ; injective = λ p → p
  }

kernelNormalSubgroup : NormalSubgroup G (c ⊔ ℓ′) ℓ
kernelNormalSubgroup = record
  { N = Kernel-rawGroup
  ; ι = Kernel.element
  ; ι-monomorphism = element-isGroupMonomorphism
  ; normal = λ n g → let module N = Kernel n in record
    { fst = record
      { element = g G.∙ N.element G.∙ g G.⁻¹
      ; inKernel = begin⟨ H.setoid ⟩
        ρ (g G.∙ N.element G.∙ g G.⁻¹)     ≈⟨ ρ.homo (g G.∙ N.element) (g G.⁻¹) ⟩
        ρ (g G.∙ N.element) H.∙ ρ (g G.⁻¹) ≈⟨ H.∙-congʳ (ρ.homo g N.element) ⟩
        ρ g H.∙ ρ N.element H.∙ ρ (g G.⁻¹) ≈⟨ H.∙-congʳ (H.∙-congˡ N.inKernel) ⟩
        ρ g H.∙ H.ε H.∙ ρ (g G.⁻¹)         ≈⟨ H.∙-congʳ (H.identityʳ (ρ g)) ⟩
        ρ g H.∙ ρ (g G.⁻¹)                 ≈⟨ ρ.homo g (g G.⁻¹) ⟨
        ρ (g G.∙ g G.⁻¹)                   ≈⟨ ρ.⟦⟧-cong (G.inverseʳ g) ⟩
        ρ G.ε                              ≈⟨ ρ.ε-homo ⟩
        H.ε                                ∎
      }
    ; snd = G.refl
    }
  }
