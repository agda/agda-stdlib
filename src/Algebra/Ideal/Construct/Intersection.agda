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

_∩_ : ∀ {c₁ ℓ₁ c₂ ℓ₂} → Ideal c₁ ℓ₁ → Ideal c₂ ℓ₂ → Ideal (ℓ ⊔ c₁ ⊔ c₂) ℓ₁
I ∩ J = record
  { I = record
    { Carrierᴹ = NSI.N.Carrier
    ; _≈ᴹ_ = NSI.N._≈_
    ; _+ᴹ_ = NSI.N._∙_
    ; _*ₗ_ = λ r ((i , j) , p) → record
      { fst = r I.I.*ₗ i , r J.I.*ₗ j
      ; snd = begin
        I.ι (r I.I.*ₗ i) ≈⟨ I.ι.*ₗ-homo r i ⟩
        r * I.ι i        ≈⟨ *-congˡ p ⟩
        r * J.ι j        ≈⟨ J.ι.*ₗ-homo r j ⟨
        J.ι (r J.I.*ₗ j) ∎
      }
    ; _*ᵣ_ = λ ((i , j) , p) r → record
      { fst = i I.I.*ᵣ r , j J.I.*ᵣ r
      ; snd = begin
        I.ι (i I.I.*ᵣ r) ≈⟨ I.ι.*ᵣ-homo r i ⟩
        I.ι i * r        ≈⟨ *-congʳ p ⟩
        J.ι j * r        ≈⟨ J.ι.*ᵣ-homo r j ⟨
        J.ι (j J.I.*ᵣ r) ∎
      }
    ; 0ᴹ = NSI.N.ε
    ; -ᴹ_ = NSI.N._⁻¹
    }
  ; ι = NSI.ι
  ; ι-monomorphism = record
    { isModuleHomomorphism = record
      { isBimoduleHomomorphism = record
        { +ᴹ-isGroupHomomorphism = NSI.ι.isGroupHomomorphism
        ; *ₗ-homo = λ r ((i , _) , _) → I.ι.*ₗ-homo r i
        ; *ᵣ-homo = λ r ((i , _) , _) → I.ι.*ᵣ-homo r i
        }
      }
    ; injective = λ p → I.ι.injective p
    }
  }
  where
    module I = Ideal I
    module J = Ideal J
    module NSI = NormalSubgroup (I.normalSubgroup NS.∩ J.normalSubgroup)

