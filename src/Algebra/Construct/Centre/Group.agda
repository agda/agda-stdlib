------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of the centre of a Group
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (AbelianGroup; Group; RawGroup)

module Algebra.Construct.Centre.Group {c ℓ} (G : Group c ℓ) where

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions using (Commutative)
open import Function.Base using (id; const; _$_; _on_)
open import Level using (_⊔_)
open import Relation.Unary using (Pred)
open import Relation.Binary.Core using (Rel)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra.Construct.Sub.Group G using (Subgroup)
open import Algebra.Construct.Sub.Group.Normal G using (IsNormal; NormalSubgroup)
open import Algebra.Properties.Group G using (∙-cancelʳ)

private
  module G = Group G


CommutesWith : Pred G.Carrier _
CommutesWith g = ∀ k → g G.∙ k G.≈ k G.∙ g

private
  open ≈-Reasoning G.setoid

  record Carrier : Set (c ⊔ ℓ) where
    field
      commuter : G.Carrier
      commutes : CommutesWith commuter

  open Carrier

  _≈_ : Rel Carrier _
  _≈_ = G._≈_ on commuter

  _∙_ : Op₂ Carrier
  g ∙ h = record
    { commuter = commuter g G.∙ commuter h
    ; commutes = λ k → begin
      (commuter g G.∙ commuter h) G.∙ k ≈⟨ G.assoc _ _ _ ⟩
      commuter g G.∙ (commuter h G.∙ k) ≈⟨ G.∙-congˡ $ commutes h k ⟩
      commuter g G.∙ (k G.∙ commuter h) ≈⟨ G.assoc _ _ _ ⟨
      commuter g G.∙ k G.∙ commuter h   ≈⟨ G.∙-congʳ $ commutes g k ⟩
      k G.∙ commuter g G.∙ commuter h   ≈⟨ G.assoc _ _ _ ⟩
      k G.∙ (commuter g G.∙ commuter h) ∎
    }

  ε : Carrier
  ε = record
    { commuter = G.ε
    ; commutes = λ k → G.trans (G.identityˡ k) (G.sym (G.identityʳ k))
    }

  _⁻¹ : Op₁ Carrier
  g ⁻¹ = record
    { commuter = commuter g G.⁻¹
    ; commutes = λ k → ∙-cancelʳ (commuter g) _ _ $ begin
        (commuter g G.⁻¹ G.∙ k) G.∙ (commuter g) ≈⟨ G.assoc _ _ _ ⟩
        commuter g G.⁻¹ G.∙ (k G.∙ commuter g)   ≈⟨ G.∙-congˡ $ commutes g k ⟨
        commuter g G.⁻¹ G.∙ (commuter g G.∙ k)   ≈⟨ G.assoc _ _ _ ⟨
        (commuter g G.⁻¹ G.∙ commuter g) G.∙ k   ≈⟨ G.∙-congʳ $ G.inverseˡ _ ⟩
        G.ε G.∙ k                                ≈⟨ commutes ε k ⟩
        k G.∙ G.ε                                ≈⟨ G.∙-congˡ $ G.inverseˡ _ ⟨
        k G.∙ (commuter g G.⁻¹ G.∙ commuter g)   ≈⟨ G.assoc _ _ _ ⟨
        (k G.∙ commuter g G.⁻¹) G.∙ (commuter g) ∎
    }

  ∙-comm : Commutative _≈_ _∙_
  ∙-comm g h = commutes g $ commuter h


open Carrier public using (commuter; commutes)

centre : NormalSubgroup _ _
centre = record
  { subgroup = record
    { domain = record
      { _≈_ = _≈_
      ; _∙_ = _∙_
      ; ε = ε
      ; _⁻¹ = _⁻¹
      }
    ; ι = commuter
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
  ; isNormal = record { conjugate = const ; normal = commutes }
  }

open NormalSubgroup centre public

abelianGroup : AbelianGroup _ _
abelianGroup = record
  {
    isAbelianGroup = record { isGroup = isGroup ; comm = ∙-comm }
  }

-- Public export

Z[_] = centre

