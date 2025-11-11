------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of the centre of a Group
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (AbelianGroup; Group; RawGroup; RawMonoid)

module Algebra.Construct.Centre.Group {c ℓ} (G : Group c ℓ) where

import Algebra.Construct.Centre.Monoid as Centre
open import Algebra.Core using (Op₁)
open import Algebra.Morphism.Structures using (IsGroupHomomorphism)
open import Function.Base using (id; _∘_; const; _$_)
open import Level using (_⊔_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Algebra.Construct.Sub.Group.Normal G using (NormalSubgroup)
open import Algebra.Properties.Group G using (∙-cancelʳ)

private
  module G = Group G
  module Z = Centre G.monoid


------------------------------------------------------------------------
-- Definition

open Z public
  using (Center; ι; central)

_⁻¹ : Op₁ Center
g ⁻¹ = record
  { ι = ι g G.⁻¹
  ; central = λ k → ∙-cancelʳ (ι g) _ _ $ begin
      (ι g G.⁻¹ G.∙ k) G.∙ (ι g) ≈⟨ G.assoc _ _ _ ⟩
      ι g G.⁻¹ G.∙ (k G.∙ ι g)   ≈⟨ G.∙-congˡ $ central g k ⟨
      ι g G.⁻¹ G.∙ (ι g G.∙ k)   ≈⟨ G.assoc _ _ _ ⟨
      (ι g G.⁻¹ G.∙ ι g) G.∙ k   ≈⟨ G.∙-congʳ $ G.inverseˡ _ ⟩
      G.ε G.∙ k                  ≈⟨ central Z.ε k ⟩
      k G.∙ G.ε                  ≈⟨ G.∙-congˡ $ G.inverseˡ _ ⟨
      k G.∙ (ι g G.⁻¹ G.∙ ι g)   ≈⟨ G.assoc _ _ _ ⟨
      (k G.∙ ι g G.⁻¹) G.∙ (ι g) ∎
  } where open ≈-Reasoning G.setoid

domain : RawGroup _ _
domain = record { RawMonoid Z.domain; _⁻¹ = _⁻¹ }

ι-isGroupHomomorphism : IsGroupHomomorphism domain _ _
ι-isGroupHomomorphism = record
  { isMonoidHomomorphism = Z.ι-isMonoidHomomorphism
  ; ⁻¹-homo = λ _ → G.refl
  }


------------------------------------------------------------------------
-- Public exports

normalSubgroup : NormalSubgroup (c ⊔ ℓ) ℓ
normalSubgroup = record
  { subgroup = record
    { ι-monomorphism = record
        { isGroupHomomorphism = ι-isGroupHomomorphism
        ; injective = id
        }
    }
  ; isNormal = record
    { conjugate = const
    ; normal = central
    }
  }
{-
open NormalSubgroup normalSubgroup public
  hiding (_⁻¹)

abelianGroup : AbelianGroup (c ⊔ ℓ) ℓ
abelianGroup = record
  { isAbelianGroup = record
    { isGroup = isGroup
    ; comm = λ g → central g ∘ ι
    }
  }

Z[_] = abelianGroup
-}
