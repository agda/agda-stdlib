------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of the centre of a Group
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles
  using (Group; AbelianGroup; RawMonoid; RawGroup)

module Algebra.Construct.Centre.Group {c ℓ} (group : Group c ℓ) where

open import Algebra.Core using (Op₁)
open import Algebra.Morphism.Structures
open import Algebra.Morphism.GroupMonomorphism using (isGroup)
open import Function.Base using (id; const; _$_)


private
  module G = Group group

open import Relation.Binary.Reasoning.Setoid G.setoid as ≈-Reasoning
open import Algebra.Properties.Group group using (∙-cancelʳ)


------------------------------------------------------------------------
-- Definition

-- Re-export the underlying sub-Monoid

open import Algebra.Construct.Centre.Monoid G.monoid as Z public
  using (Center; ι; ∙-comm)

-- Now, can define a commutative sub-Group

_⁻¹ : Op₁ Center
g ⁻¹ = record
  { ι = ι g G.⁻¹
  ; central = λ k → ∙-cancelʳ (ι g) _ _ $ begin
      (ι g G.⁻¹ G.∙ k) G.∙ (ι g) ≈⟨ G.assoc _ _ _ ⟩
      ι g G.⁻¹ G.∙ (k G.∙ ι g)   ≈⟨ G.∙-congˡ $ Center.central g k ⟨
      ι g G.⁻¹ G.∙ (ι g G.∙ k)   ≈⟨ G.assoc _ _ _ ⟨
      (ι g G.⁻¹ G.∙ ι g) G.∙ k   ≈⟨ G.∙-congʳ $ G.inverseˡ _ ⟩
      G.ε G.∙ k                  ≈⟨ Center.central Z.ε k ⟩
      k G.∙ G.ε                  ≈⟨ G.∙-congˡ $ G.inverseˡ _ ⟨
      k G.∙ (ι g G.⁻¹ G.∙ ι g)   ≈⟨ G.assoc _ _ _ ⟨
      (k G.∙ ι g G.⁻¹) G.∙ (ι g) ∎
  } where open ≈-Reasoning

domain : RawGroup _ _
domain = record { RawMonoid Z.domain; _⁻¹ = _⁻¹ }

isGroupHomomorphism : IsGroupHomomorphism domain G.rawGroup ι
isGroupHomomorphism = record
  { isMonoidHomomorphism = Z.isMonoidHomomorphism
  ; ⁻¹-homo = λ _ → G.refl
  }

isGroupMonomorphism : IsGroupMonomorphism domain G.rawGroup ι
isGroupMonomorphism = record
  { isGroupHomomorphism = isGroupHomomorphism
  ; injective = id
  }

abelianGroup : AbelianGroup _ _
abelianGroup = record
  { isAbelianGroup = record
    { isGroup = isGroup isGroupMonomorphism G.isGroup
    ; comm = ∙-comm
    }
  }

Z[_] = abelianGroup
