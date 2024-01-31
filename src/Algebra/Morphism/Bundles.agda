------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundled definitions of homomorphisms between algebras
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Morphism.Bundles where

open import Algebra.Bundles using (Magma)
open import Algebra.Morphism.Structures using (IsMagmaHomomorphism)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Morphism using (IsRelHomomorphism)
open import Relation.Binary.Morphism.Bundles using (SetoidHomomorphism)

private
  variable
    ℓ a ℓa b ℓb : Level


------------------------------------------------------------------------
-- Morphisms between Magmas
------------------------------------------------------------------------

record MagmaHomomorphism (𝓐 : Magma a ℓa) (𝓑 : Magma b ℓb) : Set (a ⊔ b ⊔ ℓa ⊔ ℓb) where
  private
    module A = Magma 𝓐
    module B = Magma 𝓑

  field
    ⟦_⟧ : A.Carrier → B.Carrier

    isMagmaHomomorphism : IsMagmaHomomorphism A.rawMagma B.rawMagma ⟦_⟧

  open IsMagmaHomomorphism isMagmaHomomorphism public

  setoidHomomorphism : SetoidHomomorphism A.setoid B.setoid
  setoidHomomorphism = record { ⟦_⟧ = ⟦_⟧ ; isRelHomomorphism = isRelHomomorphism }

