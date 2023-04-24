------------------------------------------------------------------------
-- The Agda standard library
--
-- Morphisms between algebraic lattice structures
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Core
open import Algebra.Bundles
open import Algebra.Morphism
open import Algebra.Lattice.Bundles
import Algebra.Morphism.Definitions as MorphismDefinitions
open import Level using (Level; _⊔_)
import Function.Definitions as FunctionDefinitions
open import Relation.Binary.Morphism.Structures
open import Relation.Binary.Core

module Algebra.Lattice.Morphism.Structures where

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Morphisms over lattice-like structures
------------------------------------------------------------------------

module LatticeMorphisms (L₁ : RawLattice a ℓ₁) (L₂ : RawLattice b ℓ₂) where

  open RawLattice L₁ renaming
    ( Carrier to A; _≈_ to _≈₁_
    ; _∧_ to _∧₁_; _∨_ to _∨₁_
    ; ∧-rawMagma to ∧-rawMagma₁
    ; ∨-rawMagma to ∨-rawMagma₁)

  open RawLattice L₂ renaming
    ( Carrier to B; _≈_ to _≈₂_
    ; _∧_ to _∧₂_; _∨_ to _∨₂_
    ; ∧-rawMagma to ∧-rawMagma₂
    ; ∨-rawMagma to ∨-rawMagma₂)

  module ∨ = MagmaMorphisms ∨-rawMagma₁ ∨-rawMagma₂
  module ∧ = MagmaMorphisms ∧-rawMagma₁ ∧-rawMagma₂

  open MorphismDefinitions A B _≈₂_
  open FunctionDefinitions _≈₁_ _≈₂_


  record IsLatticeHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      ∧-homo            : Homomorphic₂ ⟦_⟧ _∧₁_ _∧₂_
      ∨-homo            : Homomorphic₂ ⟦_⟧ _∨₁_ _∨₂_

    open IsRelHomomorphism isRelHomomorphism public
      renaming (cong to ⟦⟧-cong)

    ∧-isMagmaHomomorphism : ∧.IsMagmaHomomorphism ⟦_⟧
    ∧-isMagmaHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; homo = ∧-homo
      }

    ∨-isMagmaHomomorphism : ∨.IsMagmaHomomorphism ⟦_⟧
    ∨-isMagmaHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; homo = ∨-homo
      }

  record IsLatticeMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isLatticeHomomorphism : IsLatticeHomomorphism ⟦_⟧
      injective             : Injective ⟦_⟧

    open IsLatticeHomomorphism isLatticeHomomorphism public

    ∨-isMagmaMonomorphism : ∨.IsMagmaMonomorphism ⟦_⟧
    ∨-isMagmaMonomorphism = record
      { isMagmaHomomorphism = ∨-isMagmaHomomorphism
      ; injective           = injective
      }

    ∧-isMagmaMonomorphism : ∧.IsMagmaMonomorphism ⟦_⟧
    ∧-isMagmaMonomorphism = record
      { isMagmaHomomorphism = ∧-isMagmaHomomorphism
      ; injective           = injective
      }

    open ∧.IsMagmaMonomorphism ∧-isMagmaMonomorphism public
      using (isRelMonomorphism)


  record IsLatticeIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isLatticeMonomorphism : IsLatticeMonomorphism ⟦_⟧
      surjective            : Surjective ⟦_⟧

    open IsLatticeMonomorphism isLatticeMonomorphism public

    ∨-isMagmaIsomorphism : ∨.IsMagmaIsomorphism ⟦_⟧
    ∨-isMagmaIsomorphism = record
      { isMagmaMonomorphism = ∨-isMagmaMonomorphism
      ; surjective          = surjective
      }

    ∧-isMagmaIsomorphism : ∧.IsMagmaIsomorphism ⟦_⟧
    ∧-isMagmaIsomorphism = record
      { isMagmaMonomorphism = ∧-isMagmaMonomorphism
      ; surjective          = surjective
      }

    open ∧.IsMagmaIsomorphism ∧-isMagmaIsomorphism public
      using (isRelIsomorphism)

------------------------------------------------------------------------
-- Re-export contents of modules publicly

open LatticeMorphisms public
