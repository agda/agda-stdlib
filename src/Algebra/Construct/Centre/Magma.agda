------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of the centre of a Magma
--
-- NB this doesn't make sense a priori, because in the absence of
-- associativity, it's not possible to define even a Magma operation
-- on the Center type defined below, as underlying Carrier.
--
-- Yet a Magma *is* sufficient to define such a type, and thus can be
-- inherited up through the whole `Algebra.Construct.Centre.X` hierarchy.
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles using (Magma)

module Algebra.Construct.Centre.Magma {c ℓ} (G : Magma c ℓ) where

open import Algebra.Core using (Op₂)
open import Algebra.Definitions using (Central)
open import Function.Base using (id; _on_)
open import Level using (_⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Morphism.Structures
  using (IsRelHomomorphism; IsRelMonomorphism)

private
  module G = Magma G


------------------------------------------------------------------------
-- Definition

record Center : Set (c ⊔ ℓ) where
  field
    ι       : G.Carrier
    central : Central G._≈_ G._∙_ ι

open Center public

_≈_ : Rel Center _
_≈_ = G._≈_ on ι

ι-isRelHomomorphism : IsRelHomomorphism _≈_ G._≈_ ι
ι-isRelHomomorphism = record { cong = id }

ι-isRelMonomorphism : IsRelMonomorphism _≈_ G._≈_ ι
ι-isRelMonomorphism = record
  { isHomomorphism = ι-isRelHomomorphism
  ; injective = id
  }

module ι = IsRelMonomorphism ι-isRelMonomorphism

∙-comm : ∀ g h → ι g G.∙ ι h G.≈ ι h G.∙ ι g 
∙-comm g h = central g (ι h)
