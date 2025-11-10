------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of the centre of a Group
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (CommutativeSemigroup; Semigroup)

module Algebra.Construct.Centre.Semigroup {c ℓ} (G : Semigroup c ℓ) where

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions using (Central)
open import Function.Base using (id; _∘_; const; _$_; _on_)
open import Level using (_⊔_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning


------------------------------------------------------------------------
-- Definition

private
  module G = Semigroup G

  open ≈-Reasoning G.setoid

  record Center : Set (c ⊔ ℓ) where
    field
      ι       : G.Carrier
      central : Central G._≈_ G._∙_ ι

  open Center using (ι; central)

  _∙_ : Op₂ Center
  g ∙ h = record
    { ι = ι g G.∙ ι h
    ; central = λ k → begin
      (ι g G.∙ ι h) G.∙ k ≈⟨ G.assoc _ _ _ ⟩
      ι g G.∙ (ι h G.∙ k) ≈⟨ G.∙-congˡ $ central h k ⟩
      ι g G.∙ (k G.∙ ι h) ≈⟨ G.assoc _ _ _ ⟨
      ι g G.∙ k G.∙ ι h   ≈⟨ G.∙-congʳ $ central g k ⟩
      k G.∙ ι g G.∙ ι h   ≈⟨ G.assoc _ _ _ ⟩
      k G.∙ (ι g G.∙ ι h) ∎
    }

{-
------------------------------------------------------------------------
-- Public exports

normalSubgroup : NormalSubgroup (c ⊔ ℓ) ℓ
normalSubgroup = record
  { subgroup = record
    { domain = record
      { _∙_ = _∙_
      ; ε = ε
      ; _⁻¹ = _⁻¹
      }
    ; ι = ι
    ; ι-monomorphism = record
        { isGroupHomomorphism = record
          { isMonoidHomomorphism = record
            { isMagmaHomomorphism = record
              { isRelHomomorphism = record { cong = id }
              ; homo = λ _ _ → G.refl
              }
            ; ε-homo = G.refl
            }
          ; ⁻¹-homo = λ _ → G.refl
        }
      ; injective = id
      }
    }
  ; isNormal = record
    { conjugate = const
    ; normal = central
    }
  }

open NormalSubgroup normalSubgroup public

commutativeSemigroup : CommutativeSemigroup (c ⊔ ℓ) ℓ
commutativeSemigroup = record
  { isCommutativeSemigroup = record
    { isSemigroup = isSemigroup
    ; comm = λ g → central g ∘ ι
    }
  }

Z[_] = commutativeSemigroup
-}
