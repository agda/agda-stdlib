------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of the centre of an Semigroup
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles
  using (Semigroup; CommutativeSemigroup; RawMagma)

module Algebra.Construct.Centre.Semigroup
  {c ℓ} (semigroup : Semigroup c ℓ)
  where

open import Algebra.Core using (Op₂)
open import Algebra.Morphism.MagmaMonomorphism using (isSemigroup)
open import Algebra.Morphism.Structures
  using (IsMagmaHomomorphism; IsMagmaMonomorphism)
open import Function.Base using (id; _$_)

private
  module G = Semigroup semigroup

open import Algebra.Properties.Semigroup semigroup
open import Relation.Binary.Reasoning.Setoid G.setoid as ≈-Reasoning


------------------------------------------------------------------------
-- Definition

-- Re-export the underlying subtype

open import Algebra.Construct.Centre.Center G._≈_ G._∙_ as Z public
  using (Center; ι; ∙-comm)

-- Now, by associativity, a sub-Magma is definable

_∙_ : Op₂ Center
g ∙ h = record
  { ι = ι g G.∙ ι h
  ; central = λ k → begin
    (ι g G.∙ ι h) G.∙ k ≈⟨ uv≈w⇒xu∙v≈xw (Center.central h k) (ι g) ⟩
    ι g G.∙ (k G.∙ ι h) ≈⟨ uv≈w⇒u∙vx≈wx (Center.central g k) (ι h) ⟩
    k G.∙ ι g G.∙ ι h   ≈⟨ G.assoc _ _ _ ⟩
    k G.∙ (ι g G.∙ ι h) ∎
  } where open ≈-Reasoning

domain : RawMagma _ _
domain = record {_≈_ = Z._≈_; _∙_ = _∙_ }

isMagmaHomomorphism : IsMagmaHomomorphism domain G.rawMagma ι
isMagmaHomomorphism = record
  { isRelHomomorphism = Z.isRelHomomorphism
  ; homo = λ _ _ → G.refl
  }

isMagmaMonomorphism : IsMagmaMonomorphism domain G.rawMagma ι
isMagmaMonomorphism = record
  { isMagmaHomomorphism = isMagmaHomomorphism
  ; injective = id
  }

-- And hence a CommutativeSemigroup

commutativeSemigroup : CommutativeSemigroup _ _
commutativeSemigroup = record
  { isCommutativeSemigroup = record
    { isSemigroup = isSemigroup isMagmaMonomorphism G.isSemigroup
    ; comm = ∙-comm
    }
  }

Z[_] = commutativeSemigroup

