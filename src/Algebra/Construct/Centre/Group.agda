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
  using (IsGroupHomomorphism; IsGroupMonomorphism)
open import Algebra.Morphism.GroupMonomorphism using (isGroup)
open import Function.Base using (id; const; _$_)


private
  module G = Group group

open import Algebra.Properties.Group group using (∙-cancelʳ)
open import Algebra.Properties.Monoid G.monoid
  using (uv≈w⇒xu∙v≈xw)
  renaming (cancelˡ to inverse⇒cancelˡ; cancelʳ to inverse⇒cancelʳ)
open import Relation.Binary.Reasoning.Setoid G.setoid as ≈-Reasoning


------------------------------------------------------------------------
-- Definition

-- Re-export the underlying sub-Monoid

open import Algebra.Construct.Centre.Monoid G.monoid as Z public
  using (Centre; ι; ∙-comm)

-- Now, can define a commutative sub-Group

_⁻¹ : Op₁ Centre
g ⁻¹ = record
  { ι = ι g G.⁻¹
  ; central = λ k → ∙-cancelʳ (ι g) _ _ $ begin
      (ι g G.⁻¹ G.∙ k) G.∙ (ι g) ≈⟨ uv≈w⇒xu∙v≈xw (G.sym (Centre.central g k)) _ ⟩
      ι g G.⁻¹ G.∙ (ι g G.∙ k)   ≈⟨ inverse⇒cancelˡ (G.inverseˡ _) _ ⟩
      k                          ≈⟨ inverse⇒cancelʳ (G.inverseˡ _) _ ⟨
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
