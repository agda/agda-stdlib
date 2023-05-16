------------------------------------------------------------------------
-- The Agda standard library
--
-- The composition of morphisms between algebraic lattice structures.
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Algebra.Lattice.Morphism.Construct.Composition where

open import Algebra.Lattice.Bundles
open import Algebra.Lattice.Morphism.Structures
open import Function.Base using (_∘_)
import Function.Construct.Composition as Func
open import Level using (Level)
open import Relation.Binary.Morphism.Construct.Composition
open import Relation.Binary.Definitions using (Transitive)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

------------------------------------------------------------------------
-- Lattices

module _ {L₁ : RawLattice a ℓ₁}
         {L₂ : RawLattice b ℓ₂}
         {L₃ : RawLattice c ℓ₃}
         (open RawLattice)
         (≈₃-trans : Transitive (_≈_ L₃))
         {f : Carrier L₁ → Carrier L₂}
         {g : Carrier L₂ → Carrier L₃}
         where

  isLatticeHomomorphism
    : IsLatticeHomomorphism L₁ L₂ f
    → IsLatticeHomomorphism L₂ L₃ g
    → IsLatticeHomomorphism L₁ L₃ (g ∘ f)
  isLatticeHomomorphism f-homo g-homo = record
    { isRelHomomorphism = isRelHomomorphism F.isRelHomomorphism G.isRelHomomorphism
    ; ∧-homo            = λ x y → ≈₃-trans (G.⟦⟧-cong (F.∧-homo x y)) (G.∧-homo (f x) (f y))
    ; ∨-homo            = λ x y → ≈₃-trans (G.⟦⟧-cong (F.∨-homo x y)) (G.∨-homo (f x) (f y))
    } where module F = IsLatticeHomomorphism f-homo; module G = IsLatticeHomomorphism g-homo

  isLatticeMonomorphism
    : IsLatticeMonomorphism L₁ L₂ f
    → IsLatticeMonomorphism L₂ L₃ g
    → IsLatticeMonomorphism L₁ L₃ (g ∘ f)
  isLatticeMonomorphism f-mono g-mono = record
    { isLatticeHomomorphism = isLatticeHomomorphism F.isLatticeHomomorphism G.isLatticeHomomorphism
    ; injective             = F.injective ∘ G.injective
    } where module F = IsLatticeMonomorphism f-mono; module G = IsLatticeMonomorphism g-mono

  isLatticeIsomorphism
    : IsLatticeIsomorphism L₁ L₂ f
    → IsLatticeIsomorphism L₂ L₃ g
    → IsLatticeIsomorphism L₁ L₃ (g ∘ f)
  isLatticeIsomorphism f-iso g-iso = record
    { isLatticeMonomorphism = isLatticeMonomorphism F.isLatticeMonomorphism G.isLatticeMonomorphism
    ; surjective            = Func.surjective (_≈_ L₁) _ _ ≈₃-trans G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsLatticeIsomorphism f-iso; module G = IsLatticeIsomorphism g-iso
