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
import Algebra.Morphism.GroupMonomorphism as GroupMonomorphism
  using (isGroup)
open import Algebra.Structures
  using (IsGroup; IsAbelianGroup)
open import Function.Base using (id; _$_)


private
  module X = Group group

open import Algebra.Properties.Group group using (∙-cancelʳ)
open import Algebra.Properties.Monoid X.monoid
  using (uv≈w⇒xu∙v≈xw)
  renaming (cancelˡ to inverse⇒cancelˡ; cancelʳ to inverse⇒cancelʳ)
open import Relation.Binary.Reasoning.Setoid X.setoid as ≈-Reasoning


------------------------------------------------------------------------
-- Definition

-- Re-export the underlying sub-Monoid

open import Algebra.Construct.Centre.Monoid X.monoid as Z public
  using (Centre; ι; ∙-comm)

-- Now, can define a commutative sub-Group

_⁻¹ : Op₁ Centre
g ⁻¹ = record
  { ι = ι g X.⁻¹
  ; central = λ k → ∙-cancelʳ (ι g) _ _ $ begin
      (ι g X.⁻¹ X.∙ k) X.∙ (ι g) ≈⟨ uv≈w⇒xu∙v≈xw (X.sym (Centre.central g k)) _ ⟩
      ι g X.⁻¹ X.∙ (ι g X.∙ k)   ≈⟨ inverse⇒cancelˡ (X.inverseˡ _) _ ⟩
      k                          ≈⟨ inverse⇒cancelʳ (X.inverseˡ _) _ ⟨
      (k X.∙ ι g X.⁻¹) X.∙ (ι g) ∎
  } where open ≈-Reasoning

domain : RawGroup _ _
domain = record { RawMonoid Z.domain; _⁻¹ = _⁻¹ }

isGroupHomomorphism : IsGroupHomomorphism domain X.rawGroup ι
isGroupHomomorphism = record
  { isMonoidHomomorphism = Z.isMonoidHomomorphism
  ; ⁻¹-homo = λ _ → X.refl
  }

isGroupMonomorphism : IsGroupMonomorphism domain X.rawGroup ι
isGroupMonomorphism = record
  { isGroupHomomorphism = isGroupHomomorphism
  ; injective = id
  }

isGroup : IsGroup _ _ _ _
isGroup = GroupMonomorphism.isGroup isGroupMonomorphism X.isGroup

isAbelianGroup : IsAbelianGroup _ _ _ _
isAbelianGroup = record
  { isGroup = isGroup
  ; comm = ∙-comm
  }

abelianGroup : AbelianGroup _ _
abelianGroup = record { isAbelianGroup = isAbelianGroup }

Z[_] = abelianGroup
