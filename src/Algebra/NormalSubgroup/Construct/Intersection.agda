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

_∩_ : ∀ {c₁ ℓ₁ c₂ ℓ₂} → NormalSubgroup c₁ ℓ₁ → NormalSubgroup c₂ ℓ₂ → NormalSubgroup (ℓ ⊔ c₁ ⊔ c₂) ℓ₁
N ∩ M = record
  { N = record
    { Carrier = Σ[ (a , b) ∈ N.N.Carrier × M.N.Carrier ] N.ι a ≈ M.ι b
    ; _≈_ = N.N._≈_ on proj₁ on proj₁
    ; _∙_ = λ ((xₙ , xₘ) , p) ((yₙ , yₘ) , q) → record
      { fst = xₙ N.N.∙ yₙ , xₘ M.N.∙ yₘ
      ; snd = begin
        N.ι (xₙ N.N.∙ yₙ) ≈⟨ N.ι.∙-homo xₙ yₙ ⟩
        N.ι xₙ ∙ N.ι yₙ   ≈⟨ ∙-cong p q ⟩
        M.ι xₘ ∙ M.ι yₘ   ≈⟨ M.ι.∙-homo xₘ yₘ ⟨
        M.ι (xₘ M.N.∙ yₘ) ∎
      }
    ; ε = record
      { fst = N.N.ε , M.N.ε
      ; snd = begin
        N.ι N.N.ε ≈⟨ N.ι.ε-homo ⟩
        ε         ≈⟨ M.ι.ε-homo ⟨
        M.ι M.N.ε ∎
      }
    ; _⁻¹ = λ ((n , m) , p) → record
      { fst = n N.N.⁻¹ , m M.N.⁻¹
      ; snd = begin
        N.ι (n N.N.⁻¹) ≈⟨ N.ι.⁻¹-homo n ⟩
        N.ι n ⁻¹       ≈⟨ ⁻¹-cong p ⟩
        M.ι m ⁻¹       ≈⟨ M.ι.⁻¹-homo m ⟨
        M.ι (m M.N.⁻¹) ∎
      }
    }
  ; ι = λ ((n , _) , _) → N.ι n
  ; ι-monomorphism = record
    { isGroupHomomorphism = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record
            { cong = N.ι.⟦⟧-cong
            }
          ; homo = λ ((x , _) , _) ((y , _) , _) → N.ι.∙-homo x y
          }
        ; ε-homo = N.ι.ε-homo
        }
      ; ⁻¹-homo = λ ((x , _) , _) → N.ι.⁻¹-homo x
      }
    ; injective = λ p → N.ι.injective p
    }
  ; normal = λ ((n , m) , p) g → record
    { fst = record
      { fst = proj₁ (N.normal n g) , proj₁ (M.normal m g)
      ; snd = begin
        N.ι (proj₁ (N.normal n g)) ≈⟨ proj₂ (N.normal n g) ⟨
        g ∙ N.ι n ∙ g ⁻¹           ≈⟨ ∙-congʳ (∙-cong refl p) ⟩
        g ∙ M.ι m ∙ g ⁻¹           ≈⟨ proj₂ (M.normal m g) ⟩
        M.ι (proj₁ (M.normal m g)) ∎
      }
    ; snd = proj₂ (N.normal n g)
    }
  }
  where
    module N = NormalSubgroup N
    module M = NormalSubgroup M
