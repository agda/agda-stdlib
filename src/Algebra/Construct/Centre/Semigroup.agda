------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of Z[ G ] the centre of a Semigroup
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (CommutativeSemigroup; Semigroup; RawMagma)

module Algebra.Construct.Centre.Semigroup {c ℓ} (G : Semigroup c ℓ) where

import Algebra.Construct.Centre.Magma as Centre
open import Algebra.Core using (Op₂)
open import Algebra.Definitions using (Commutative)
open import Algebra.Morphism.Structures using (IsMagmaMonomorphism)
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
  using (Center; ι; central; ∙-comm)
  hiding (module ι)
  
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

ι-isMagmaMonomorphism : IsMagmaMonomorphism domain G.rawMagma ι
ι-isMagmaMonomorphism = record
  { isMagmaHomomorphism = record
    { isRelHomomorphism = Z.ι.isHomomorphism
    ; homo = λ _ _ → G.refl
    }
  ; injective = id
  }

module ι = IsMagmaMonomorphism ι-isMagmaMonomorphism


------------------------------------------------------------------------
-- Public exports

submagma : Subsemigroup.Submagma _ _
submagma = record { ι-monomorphism = ι-isMagmaMonomorphism }

semigroup : Semigroup _ _
semigroup = Subsemigroup.semigroup submagma

commutativeSemigroup : CommutativeSemigroup _ _
commutativeSemigroup = record
  { isCommutativeSemigroup = record
    { isSemigroup = isSemigroup
    ; comm = ∙-comm
    }
  }
  where open Semigroup semigroup using (isSemigroup)

Z[_] = commutativeSemigroup
