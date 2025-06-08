------------------------------------------------------------------------
-- Intersection of normal subgroups
--
-- The Agda standard library
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles

module Algebra.NormalSubgroup.Construct.Intersection {c ℓ} (G : Group c ℓ) where

open Group G

open import Algebra.NormalSubgroup G
open import Data.Product.Base
open import Function.Base
open import Level
open import Relation.Binary.Reasoning.Setoid setoid

record ICarrier {c₁ ℓ₁ c₂ ℓ₂} (N : NormalSubgroup c₁ ℓ₁) (M : NormalSubgroup c₂ ℓ₂) : Set (ℓ ⊔ c₁ ⊔ c₂) where
  constructor icarrier
  private
    module N = NormalSubgroup N
    module M = NormalSubgroup M
  field
    {a} : N.N.Carrier
    {b} : M.N.Carrier
    a≈b : N.ι a ≈ M.ι b

_∩_ : ∀ {c₁ ℓ₁ c₂ ℓ₂} → NormalSubgroup c₁ ℓ₁ → NormalSubgroup c₂ ℓ₂ → NormalSubgroup (ℓ ⊔ c₁ ⊔ c₂) ℓ₁
N ∩ M = record
  { N = record
    { Carrier = ICarrier N M
    ; _≈_ = N.N._≈_ on ICarrier.a
    ; _∙_ = λ p q → record
      { a≈b = begin
        N.ι (_ N.N.∙ _) ≈⟨ N.ι.∙-homo _ _ ⟩
        N.ι _ ∙ N.ι _   ≈⟨ ∙-cong (ICarrier.a≈b p) (ICarrier.a≈b q) ⟩
        M.ι _ ∙ M.ι _   ≈⟨ M.ι.∙-homo _ _ ⟨
        M.ι (_ M.N.∙ _) ∎
      }
    ; ε = record
      { a≈b = begin
        N.ι N.N.ε ≈⟨ N.ι.ε-homo ⟩
        ε         ≈⟨ M.ι.ε-homo ⟨
        M.ι M.N.ε ∎
      }
    ; _⁻¹ = λ p → record
      { a≈b = begin
        N.ι (_ N.N.⁻¹) ≈⟨ N.ι.⁻¹-homo _ ⟩
        N.ι _ ⁻¹       ≈⟨ ⁻¹-cong (ICarrier.a≈b p) ⟩
        M.ι _ ⁻¹       ≈⟨ M.ι.⁻¹-homo _ ⟨
        M.ι (_ M.N.⁻¹) ∎
      }
    }
  ; ι = λ p → N.ι _
  ; ι-monomorphism = record
    { isGroupHomomorphism = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record
            { cong = N.ι.⟦⟧-cong
            }
          ; homo = λ p q → N.ι.∙-homo _ _
          }
        ; ε-homo = N.ι.ε-homo
        }
      ; ⁻¹-homo = λ p → N.ι.⁻¹-homo _
      }
    ; injective = λ p → N.ι.injective p
    }
  ; normal = λ p g → record
    { fst = record
      { a≈b = begin
        N.ι (proj₁ (N.normal _ g)) ≈⟨ proj₂ (N.normal _ g) ⟨
        g ∙ N.ι _ ∙ g ⁻¹           ≈⟨ ∙-congʳ (∙-congˡ (ICarrier.a≈b p)) ⟩
        g ∙ M.ι _ ∙ g ⁻¹           ≈⟨ proj₂ (M.normal _ g) ⟩
        M.ι (proj₁ (M.normal _ g)) ∎
      }
    ; snd = proj₂ (N.normal _ g)
    }
  }
  where
    module N = NormalSubgroup N
    module M = NormalSubgroup M


