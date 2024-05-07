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
    ℓ m ℓm n ℓn : Level


------------------------------------------------------------------------
-- Morphisms between Magmas
------------------------------------------------------------------------

record MagmaHomomorphism (M : Magma m ℓm) (N : Magma n ℓn) : Set (m ⊔ n ⊔ ℓm ⊔ ℓn) where
  private
    module M = Magma M
    module N = Magma N

  field
    ⟦_⟧ : M.Carrier → N.Carrier

    isMagmaHomomorphism : IsMagmaHomomorphism M.rawMagma N.rawMagma ⟦_⟧

  open IsMagmaHomomorphism isMagmaHomomorphism public

  setoidHomomorphism : SetoidHomomorphism M.setoid N.setoid
  setoidHomomorphism = record { ⟦_⟧ = ⟦_⟧ ; isRelHomomorphism = isRelHomomorphism }

