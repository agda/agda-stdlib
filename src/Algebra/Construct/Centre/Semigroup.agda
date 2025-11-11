------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of the centre of a Group
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (CommutativeSemigroup; Semigroup; RawMagma)

module Algebra.Construct.Centre.Semigroup {c ℓ} (G : Semigroup c ℓ) where

import Algebra.Construct.Centre.Magma as Centre
open import Algebra.Core using (Op₂)
open import Algebra.Morphism.Structures using (IsMagmaHomomorphism)
open import Function.Base using (id; _∘_; const; _$_; _on_)
open import Level using (_⊔_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

import Algebra.Construct.Sub.Semigroup G as Subsemigroup

private
  module G = Semigroup G
  module Z = Centre G.magma


------------------------------------------------------------------------
-- Definition

open Z public
  using (Center; ι; central)
  
_∙_ : Op₂ Center
ι       (g ∙ h) = ι g G.∙ ι h
central (g ∙ h) = λ k → begin
  (ι g G.∙ ι h) G.∙ k ≈⟨ G.assoc _ _ _ ⟩
  ι g G.∙ (ι h G.∙ k) ≈⟨ G.∙-congˡ $ central h k ⟩
  ι g G.∙ (k G.∙ ι h) ≈⟨ G.assoc _ _ _ ⟨
  ι g G.∙ k G.∙ ι h   ≈⟨ G.∙-congʳ $ central g k ⟩
  k G.∙ ι g G.∙ ι h   ≈⟨ G.assoc _ _ _ ⟩
  k G.∙ (ι g G.∙ ι h) ∎
  where open ≈-Reasoning G.setoid

domain : RawMagma _ _
domain = record { _≈_ = Z._≈_; _∙_ = _∙_ }

ι-isMagmaHomomorphism : IsMagmaHomomorphism domain G.rawMagma ι
ι-isMagmaHomomorphism = record
  { isRelHomomorphism = Z.ι-isRelHomomorphism
  ; homo = λ _ _ → G.refl
  }


------------------------------------------------------------------------
-- Public exports

semigroup : Semigroup _ _
semigroup = Subsemigroup.semigroup record
  { ι-monomorphism = record
    { isMagmaHomomorphism = ι-isMagmaHomomorphism
    ; injective = id
    }
  }

commutativeSemigroup : CommutativeSemigroup _ _
commutativeSemigroup = record
  { isCommutativeSemigroup = record
    { isSemigroup = isSemigroup
    ; comm = λ g → central g ∘ ι
    }
  }
  where open Semigroup semigroup using (isSemigroup)

Z[_] = commutativeSemigroup
