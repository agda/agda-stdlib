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
open import Algebra.Morphism.Structures using (IsMagmaMonomorphism)
open import Function.Base using (id)

private
  module X = Semigroup semigroup

open import Algebra.Properties.Semigroup semigroup
open import Relation.Binary.Reasoning.Setoid X.setoid as ≈-Reasoning


------------------------------------------------------------------------
-- Definition

-- Re-export the underlying subtype

open import Algebra.Construct.Centre.Centre X._≈_ X._∙_ as Z public
  using (Centre; ι; ∙-comm)

-- Now, by associativity, a sub-Magma is definable

domain : RawMagma _ _
domain = record {_≈_ = Z._≈_; _∙_ = _∙_ }
  where
  _∙_ : Op₂ Centre
  g ∙ h = record
    { ι = ι g X.∙ ι h
    ; central = λ k → begin
      (ι g X.∙ ι h) X.∙ k ≈⟨ uv≈w⇒xu∙v≈xw (Centre.central h k) (ι g) ⟩
      ι g X.∙ (k X.∙ ι h) ≈⟨ uv≈w⇒u∙vx≈wx (Centre.central g k) (ι h) ⟩
      k X.∙ ι g X.∙ ι h   ≈⟨ X.assoc _ _ _ ⟩
      k X.∙ (ι g X.∙ ι h) ∎
    } where open ≈-Reasoning

isMagmaMonomorphism : IsMagmaMonomorphism domain X.rawMagma ι
isMagmaMonomorphism = record
  { isMagmaHomomorphism = record
    { isRelHomomorphism = Z.isRelHomomorphism
    ; homo = λ _ _ → X.refl
    }
    ; injective = id
  }

-- Public export of the sub-X-homomorphisms

open IsMagmaMonomorphism isMagmaMonomorphism public

-- And hence a CommutativeSemigroup

commutativeSemigroup : CommutativeSemigroup _ _
commutativeSemigroup = record
  { isCommutativeSemigroup = record
    { isSemigroup = isSemigroup isMagmaMonomorphism X.isSemigroup
    ; comm = ∙-comm
    }
  }

-- Public export of the sub-X-structures/bundles

open CommutativeSemigroup commutativeSemigroup public

-- Public export of the bundle

Z[_] = commutativeSemigroup

