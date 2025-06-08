------------------------------------------------------------------------
-- Intersection of ideals
--
-- The Agda standard library
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles

module Algebra.Ideal.Construct.Intersection {c ℓ} (R : Ring c ℓ) where

open Ring R

open import Algebra.NormalSubgroup
import Algebra.NormalSubgroup.Construct.Intersection +-group as NS
open import Algebra.Ideal R
open import Data.Product.Base
open import Function.Base
open import Level
open import Relation.Binary.Reasoning.Setoid setoid

open NS public using (ICarrier; icarrier)

_∩_ : ∀ {c₁ ℓ₁ c₂ ℓ₂} → Ideal c₁ ℓ₁ → Ideal c₂ ℓ₂ → Ideal (ℓ ⊔ c₁ ⊔ c₂) ℓ₁
I ∩ J = record
  { I = record
    { Carrierᴹ = NSI.N.Carrier
    ; _≈ᴹ_ = NSI.N._≈_
    ; _+ᴹ_ = NSI.N._∙_
    ; _*ₗ_ = λ r p → record
      { a≈b = begin
        I.ι (r I.I.*ₗ _) ≈⟨ I.ι.*ₗ-homo r _ ⟩
        r * I.ι _        ≈⟨ *-congˡ (NS.ICarrier.a≈b p) ⟩
        r * J.ι _        ≈⟨ J.ι.*ₗ-homo r _ ⟨
        J.ι (r J.I.*ₗ _) ∎
      }
    ; _*ᵣ_ = λ p r → record
      { a≈b = begin
        I.ι (_ I.I.*ᵣ r) ≈⟨ I.ι.*ᵣ-homo r _ ⟩
        I.ι _ * r        ≈⟨ *-congʳ (NS.ICarrier.a≈b p) ⟩
        J.ι _ * r        ≈⟨ J.ι.*ᵣ-homo r _ ⟨
        J.ι (_ J.I.*ᵣ r) ∎
      }
    ; 0ᴹ = NSI.N.ε
    ; -ᴹ_ = NSI.N._⁻¹
    }
  ; ι = NSI.ι
  ; ι-monomorphism = record
    { isModuleHomomorphism = record
      { isBimoduleHomomorphism = record
        { +ᴹ-isGroupHomomorphism = NSI.ι.isGroupHomomorphism
        ; *ₗ-homo = λ r p → I.ι.*ₗ-homo r _
        ; *ᵣ-homo = λ r p → I.ι.*ᵣ-homo r _
        }
      }
    ; injective = λ p → I.ι.injective p
    }
  }
  where
    module I = Ideal I
    module J = Ideal J
    module NSI = NormalSubgroup (I.normalSubgroup NS.∩ J.normalSubgroup)

