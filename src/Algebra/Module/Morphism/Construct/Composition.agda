------------------------------------------------------------------------
-- The Agda standard library
--
-- The composition of morphisms between module-like algebraic structures.
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Algebra.Module.Morphism.Construct.Composition where

open import Algebra.Bundles
open import Algebra.Module.Bundles
open import Algebra.Module.Morphism.Structures
open import Algebra.Morphism.Construct.Composition
open import Function.Base using (_∘_)
import Function.Construct.Composition as Func
open import Level using (Level)

private
  variable
    r ℓr s ℓs m₁ ℓm₁ m₂ ℓm₂ m₃ ℓm₃ : Level

module _
  {semiring : Semiring r ℓr}
  {M₁ : LeftSemimodule semiring m₁ ℓm₁}
  {M₂ : LeftSemimodule semiring m₂ ℓm₂}
  {M₃ : LeftSemimodule semiring m₃ ℓm₃}
  (open LeftSemimodule)
  {f : Carrierᴹ M₁ → Carrierᴹ M₂}
  {g : Carrierᴹ M₂ → Carrierᴹ M₃}
  where

  isLeftSemimoduleHomomorphism : IsLeftSemimoduleHomomorphism M₁ M₂ f →
                                 IsLeftSemimoduleHomomorphism M₂ M₃ g →
                                 IsLeftSemimoduleHomomorphism M₁ M₃ (g ∘ f)
  isLeftSemimoduleHomomorphism f-homo g-homo = record
    { +ᴹ-isMonoidHomomorphism = isMonoidHomomorphism (≈ᴹ-trans M₃) F.+ᴹ-isMonoidHomomorphism G.+ᴹ-isMonoidHomomorphism
    ; *ₗ-homo                 = λ r x → ≈ᴹ-trans M₃ (G.⟦⟧-cong (F.*ₗ-homo r x)) (G.*ₗ-homo r (f x))
    } where module F = IsLeftSemimoduleHomomorphism f-homo; module G = IsLeftSemimoduleHomomorphism g-homo

  isLeftSemimoduleMonomorphism : IsLeftSemimoduleMonomorphism M₁ M₂ f →
                                 IsLeftSemimoduleMonomorphism M₂ M₃ g →
                                 IsLeftSemimoduleMonomorphism M₁ M₃ (g ∘ f)
  isLeftSemimoduleMonomorphism f-mono g-mono = record
    { isLeftSemimoduleHomomorphism = isLeftSemimoduleHomomorphism F.isLeftSemimoduleHomomorphism G.isLeftSemimoduleHomomorphism
    ; injective                    = F.injective ∘ G.injective
    } where module F = IsLeftSemimoduleMonomorphism f-mono; module G = IsLeftSemimoduleMonomorphism g-mono

  isLeftSemimoduleIsomorphism : IsLeftSemimoduleIsomorphism M₁ M₂ f →
                                IsLeftSemimoduleIsomorphism M₂ M₃ g →
                                IsLeftSemimoduleIsomorphism M₁ M₃ (g ∘ f)
  isLeftSemimoduleIsomorphism f-iso g-iso = record
    { isLeftSemimoduleMonomorphism = isLeftSemimoduleMonomorphism F.isLeftSemimoduleMonomorphism G.isLeftSemimoduleMonomorphism
    ; surjective                   = Func.surjective (_≈ᴹ_ M₁) _ _ (≈ᴹ-trans M₃) G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsLeftSemimoduleIsomorphism f-iso; module G = IsLeftSemimoduleIsomorphism g-iso

module _
  {ring : Ring r ℓr}
  {M₁ : LeftModule ring m₁ ℓm₁}
  {M₂ : LeftModule ring m₂ ℓm₂}
  {M₃ : LeftModule ring m₃ ℓm₃}
  (open LeftModule)
  {f : Carrierᴹ M₁ → Carrierᴹ M₂}
  {g : Carrierᴹ M₂ → Carrierᴹ M₃}
  where

  isLeftModuleHomomorphism : IsLeftModuleHomomorphism M₁ M₂ f →
                             IsLeftModuleHomomorphism M₂ M₃ g →
                             IsLeftModuleHomomorphism M₁ M₃ (g ∘ f)
  isLeftModuleHomomorphism f-homo g-homo = record
    { +ᴹ-isGroupHomomorphism = isGroupHomomorphism (≈ᴹ-trans M₃) F.+ᴹ-isGroupHomomorphism G.+ᴹ-isGroupHomomorphism
    ; *ₗ-homo = λ r x → ≈ᴹ-trans M₃ (G.⟦⟧-cong (F.*ₗ-homo r x)) (G.*ₗ-homo r (f x))
    } where module F = IsLeftModuleHomomorphism f-homo; module G = IsLeftModuleHomomorphism g-homo

  isLeftModuleMonomorphism : IsLeftModuleMonomorphism M₁ M₂ f →
                             IsLeftModuleMonomorphism M₂ M₃ g →
                             IsLeftModuleMonomorphism M₁ M₃ (g ∘ f)
  isLeftModuleMonomorphism f-mono g-mono = record
    { isLeftModuleHomomorphism = isLeftModuleHomomorphism F.isLeftModuleHomomorphism G.isLeftModuleHomomorphism
    ; injective                = F.injective ∘ G.injective
    } where module F = IsLeftModuleMonomorphism f-mono; module G = IsLeftModuleMonomorphism g-mono

  isLeftModuleIsomorphism : IsLeftModuleIsomorphism M₁ M₂ f →
                            IsLeftModuleIsomorphism M₂ M₃ g →
                            IsLeftModuleIsomorphism M₁ M₃ (g ∘ f)
  isLeftModuleIsomorphism f-iso g-iso = record
    { isLeftModuleMonomorphism = isLeftModuleMonomorphism F.isLeftModuleMonomorphism G.isLeftModuleMonomorphism
    ; surjective               = Func.surjective (_≈ᴹ_ M₁) _ _ (≈ᴹ-trans M₃) G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsLeftModuleIsomorphism f-iso; module G = IsLeftModuleIsomorphism g-iso

module _
  {semiring : Semiring r ℓr}
  {M₁ : RightSemimodule semiring m₁ ℓm₁}
  {M₂ : RightSemimodule semiring m₂ ℓm₂}
  {M₃ : RightSemimodule semiring m₃ ℓm₃}
  (open RightSemimodule)
  {f : Carrierᴹ M₁ → Carrierᴹ M₂}
  {g : Carrierᴹ M₂ → Carrierᴹ M₃}
  where

  isRightSemimoduleHomomorphism : IsRightSemimoduleHomomorphism M₁ M₂ f →
                                  IsRightSemimoduleHomomorphism M₂ M₃ g →
                                  IsRightSemimoduleHomomorphism M₁ M₃ (g ∘ f)
  isRightSemimoduleHomomorphism f-homo g-homo = record
    { +ᴹ-isMonoidHomomorphism = isMonoidHomomorphism (≈ᴹ-trans M₃) F.+ᴹ-isMonoidHomomorphism G.+ᴹ-isMonoidHomomorphism
    ; *ᵣ-homo                 = λ r x → ≈ᴹ-trans M₃ (G.⟦⟧-cong (F.*ᵣ-homo r x)) (G.*ᵣ-homo r (f x))
    } where module F = IsRightSemimoduleHomomorphism f-homo; module G = IsRightSemimoduleHomomorphism g-homo

  isRightSemimoduleMonomorphism : IsRightSemimoduleMonomorphism M₁ M₂ f →
                                  IsRightSemimoduleMonomorphism M₂ M₃ g →
                                  IsRightSemimoduleMonomorphism M₁ M₃ (g ∘ f)
  isRightSemimoduleMonomorphism f-mono g-mono = record
    { isRightSemimoduleHomomorphism = isRightSemimoduleHomomorphism F.isRightSemimoduleHomomorphism G.isRightSemimoduleHomomorphism
    ; injective                     = F.injective ∘ G.injective
    } where module F = IsRightSemimoduleMonomorphism f-mono; module G = IsRightSemimoduleMonomorphism g-mono

  isRightSemimoduleIsomorphism : IsRightSemimoduleIsomorphism M₁ M₂ f →
                                 IsRightSemimoduleIsomorphism M₂ M₃ g →
                                 IsRightSemimoduleIsomorphism M₁ M₃ (g ∘ f)
  isRightSemimoduleIsomorphism f-iso g-iso = record
    { isRightSemimoduleMonomorphism = isRightSemimoduleMonomorphism F.isRightSemimoduleMonomorphism G.isRightSemimoduleMonomorphism
    ; surjective                    = Func.surjective (_≈ᴹ_ M₁) _ _ (≈ᴹ-trans M₃) G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsRightSemimoduleIsomorphism f-iso; module G = IsRightSemimoduleIsomorphism g-iso

module _
  {ring : Ring r ℓr}
  {M₁ : RightModule ring m₁ ℓm₁}
  {M₂ : RightModule ring m₂ ℓm₂}
  {M₃ : RightModule ring m₃ ℓm₃}
  (open RightModule)
  {f : Carrierᴹ M₁ → Carrierᴹ M₂}
  {g : Carrierᴹ M₂ → Carrierᴹ M₃}
  where

  isRightModuleHomomorphism : IsRightModuleHomomorphism M₁ M₂ f →
                              IsRightModuleHomomorphism M₂ M₃ g →
                              IsRightModuleHomomorphism M₁ M₃ (g ∘ f)
  isRightModuleHomomorphism f-homo g-homo = record
    { +ᴹ-isGroupHomomorphism = isGroupHomomorphism (≈ᴹ-trans M₃) F.+ᴹ-isGroupHomomorphism G.+ᴹ-isGroupHomomorphism
    ; *ᵣ-homo                = λ r x → ≈ᴹ-trans M₃ (G.⟦⟧-cong (F.*ᵣ-homo r x)) (G.*ᵣ-homo r (f x))
    } where module F = IsRightModuleHomomorphism f-homo; module G = IsRightModuleHomomorphism g-homo

  isRightModuleMonomorphism : IsRightModuleMonomorphism M₁ M₂ f →
                              IsRightModuleMonomorphism M₂ M₃ g →
                              IsRightModuleMonomorphism M₁ M₃ (g ∘ f)
  isRightModuleMonomorphism f-mono g-mono = record
    { isRightModuleHomomorphism = isRightModuleHomomorphism F.isRightModuleHomomorphism G.isRightModuleHomomorphism
    ; injective                 = F.injective ∘ G.injective
    } where module F = IsRightModuleMonomorphism f-mono; module G = IsRightModuleMonomorphism g-mono

  isRightModuleIsomorphism : IsRightModuleIsomorphism M₁ M₂ f →
                             IsRightModuleIsomorphism M₂ M₃ g →
                             IsRightModuleIsomorphism M₁ M₃ (g ∘ f)
  isRightModuleIsomorphism f-iso g-iso = record
    { isRightModuleMonomorphism = isRightModuleMonomorphism F.isRightModuleMonomorphism G.isRightModuleMonomorphism
    ; surjective                = Func.surjective (_≈ᴹ_ M₁) _ _ (≈ᴹ-trans M₃) G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsRightModuleIsomorphism f-iso; module G = IsRightModuleIsomorphism g-iso

module _
  {R-semiring : Semiring r ℓr}
  {S-semiring : Semiring s ℓs}
  {M₁ : Bisemimodule R-semiring S-semiring m₁ ℓm₁}
  {M₂ : Bisemimodule R-semiring S-semiring m₂ ℓm₂}
  {M₃ : Bisemimodule R-semiring S-semiring m₃ ℓm₃}
  (open Bisemimodule)
  {f : Carrierᴹ M₁ → Carrierᴹ M₂}
  {g : Carrierᴹ M₂ → Carrierᴹ M₃}
  where

  isBisemimoduleHomomorphism : IsBisemimoduleHomomorphism M₁ M₂ f →
                               IsBisemimoduleHomomorphism M₂ M₃ g →
                               IsBisemimoduleHomomorphism M₁ M₃ (g ∘ f)
  isBisemimoduleHomomorphism f-homo g-homo = record
    { +ᴹ-isMonoidHomomorphism = isMonoidHomomorphism (≈ᴹ-trans M₃) F.+ᴹ-isMonoidHomomorphism G.+ᴹ-isMonoidHomomorphism
    ; *ₗ-homo                 = λ r x → ≈ᴹ-trans M₃ (G.⟦⟧-cong (F.*ₗ-homo r x)) (G.*ₗ-homo r (f x))
    ; *ᵣ-homo                 = λ r x → ≈ᴹ-trans M₃ (G.⟦⟧-cong (F.*ᵣ-homo r x)) (G.*ᵣ-homo r (f x))
    } where module F = IsBisemimoduleHomomorphism f-homo; module G = IsBisemimoduleHomomorphism g-homo

  isBisemimoduleMonomorphism : IsBisemimoduleMonomorphism M₁ M₂ f →
                               IsBisemimoduleMonomorphism M₂ M₃ g →
                               IsBisemimoduleMonomorphism M₁ M₃ (g ∘ f)
  isBisemimoduleMonomorphism f-mono g-mono = record
    { isBisemimoduleHomomorphism = isBisemimoduleHomomorphism F.isBisemimoduleHomomorphism G.isBisemimoduleHomomorphism
    ; injective                  = F.injective ∘ G.injective
    } where module F = IsBisemimoduleMonomorphism f-mono; module G = IsBisemimoduleMonomorphism g-mono

  isBisemimoduleIsomorphism : IsBisemimoduleIsomorphism M₁ M₂ f →
                              IsBisemimoduleIsomorphism M₂ M₃ g →
                              IsBisemimoduleIsomorphism M₁ M₃ (g ∘ f)
  isBisemimoduleIsomorphism f-iso g-iso = record
    { isBisemimoduleMonomorphism = isBisemimoduleMonomorphism F.isBisemimoduleMonomorphism G.isBisemimoduleMonomorphism
    ; surjective                 = Func.surjective (_≈ᴹ_ M₁) _ _ (≈ᴹ-trans M₃) G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsBisemimoduleIsomorphism f-iso; module G = IsBisemimoduleIsomorphism g-iso

module _
  {R-ring : Ring r ℓr}
  {S-ring : Ring s ℓs}
  {M₁ : Bimodule R-ring S-ring m₁ ℓm₁}
  {M₂ : Bimodule R-ring S-ring m₂ ℓm₂}
  {M₃ : Bimodule R-ring S-ring m₃ ℓm₃}
  (open Bimodule)
  {f : Carrierᴹ M₁ → Carrierᴹ M₂}
  {g : Carrierᴹ M₂ → Carrierᴹ M₃}
  where

  isBimoduleHomomorphism : IsBimoduleHomomorphism M₁ M₂ f →
                           IsBimoduleHomomorphism M₂ M₃ g →
                           IsBimoduleHomomorphism M₁ M₃ (g ∘ f)
  isBimoduleHomomorphism f-homo g-homo = record
    { +ᴹ-isGroupHomomorphism = isGroupHomomorphism (≈ᴹ-trans M₃) F.+ᴹ-isGroupHomomorphism G.+ᴹ-isGroupHomomorphism
    ; *ₗ-homo                = λ r x → ≈ᴹ-trans M₃ (G.⟦⟧-cong (F.*ₗ-homo r x)) (G.*ₗ-homo r (f x))
    ; *ᵣ-homo                = λ r x → ≈ᴹ-trans M₃ (G.⟦⟧-cong (F.*ᵣ-homo r x)) (G.*ᵣ-homo r (f x))
    } where module F = IsBimoduleHomomorphism f-homo; module G = IsBimoduleHomomorphism g-homo

  isBimoduleMonomorphism : IsBimoduleMonomorphism M₁ M₂ f →
                           IsBimoduleMonomorphism M₂ M₃ g →
                           IsBimoduleMonomorphism M₁ M₃ (g ∘ f)
  isBimoduleMonomorphism f-mono g-mono = record
    { isBimoduleHomomorphism = isBimoduleHomomorphism F.isBimoduleHomomorphism G.isBimoduleHomomorphism
    ; injective              = F.injective ∘ G.injective
    } where module F = IsBimoduleMonomorphism f-mono; module G = IsBimoduleMonomorphism g-mono

  isBimoduleIsomorphism : IsBimoduleIsomorphism M₁ M₂ f →
                          IsBimoduleIsomorphism M₂ M₃ g →
                          IsBimoduleIsomorphism M₁ M₃ (g ∘ f)
  isBimoduleIsomorphism f-iso g-iso = record
    { isBimoduleMonomorphism = isBimoduleMonomorphism F.isBimoduleMonomorphism G.isBimoduleMonomorphism
    ; surjective             = Func.surjective (_≈ᴹ_ M₁) _ _ (≈ᴹ-trans M₃) G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsBimoduleIsomorphism f-iso; module G = IsBimoduleIsomorphism g-iso

module _
  {commutativeSemiring : CommutativeSemiring r ℓr}
  {M₁ : Semimodule commutativeSemiring m₁ ℓm₁}
  {M₂ : Semimodule commutativeSemiring m₂ ℓm₂}
  {M₃ : Semimodule commutativeSemiring m₃ ℓm₃}
  (open Semimodule)
  {f : Carrierᴹ M₁ → Carrierᴹ M₂}
  {g : Carrierᴹ M₂ → Carrierᴹ M₃}
  where

  isSemimoduleHomomorphism : IsSemimoduleHomomorphism M₁ M₂ f →
                             IsSemimoduleHomomorphism M₂ M₃ g →
                             IsSemimoduleHomomorphism M₁ M₃ (g ∘ f)
  isSemimoduleHomomorphism f-homo g-homo = record
    { isBisemimoduleHomomorphism = isBisemimoduleHomomorphism F.isBisemimoduleHomomorphism G.isBisemimoduleHomomorphism
    } where module F = IsSemimoduleHomomorphism f-homo; module G = IsSemimoduleHomomorphism g-homo

  isSemimoduleMonomorphism : IsSemimoduleMonomorphism M₁ M₂ f →
                             IsSemimoduleMonomorphism M₂ M₃ g →
                             IsSemimoduleMonomorphism M₁ M₃ (g ∘ f)
  isSemimoduleMonomorphism f-mono g-mono = record
    { isSemimoduleHomomorphism = isSemimoduleHomomorphism F.isSemimoduleHomomorphism G.isSemimoduleHomomorphism
    ; injective                = F.injective ∘ G.injective
    } where module F = IsSemimoduleMonomorphism f-mono; module G = IsSemimoduleMonomorphism g-mono

  isSemimoduleIsomorphism : IsSemimoduleIsomorphism M₁ M₂ f →
                            IsSemimoduleIsomorphism M₂ M₃ g →
                            IsSemimoduleIsomorphism M₁ M₃ (g ∘ f)
  isSemimoduleIsomorphism f-iso g-iso = record
    { isSemimoduleMonomorphism = isSemimoduleMonomorphism F.isSemimoduleMonomorphism G.isSemimoduleMonomorphism
    ; surjective               = Func.surjective (_≈ᴹ_ M₁) _ _ (≈ᴹ-trans M₃) G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsSemimoduleIsomorphism f-iso; module G = IsSemimoduleIsomorphism g-iso

module _
  {commutativeRing : CommutativeRing r ℓr}
  {M₁ : Module commutativeRing m₁ ℓm₁}
  {M₂ : Module commutativeRing m₂ ℓm₂}
  {M₃ : Module commutativeRing m₃ ℓm₃}
  (open Module)
  {f : Carrierᴹ M₁ → Carrierᴹ M₂}
  {g : Carrierᴹ M₂ → Carrierᴹ M₃}
  where

  isModuleHomomorphism : IsModuleHomomorphism M₁ M₂ f →
                         IsModuleHomomorphism M₂ M₃ g →
                         IsModuleHomomorphism M₁ M₃ (g ∘ f)
  isModuleHomomorphism f-homo g-homo = record
    { isBimoduleHomomorphism = isBimoduleHomomorphism F.isBimoduleHomomorphism G.isBimoduleHomomorphism
    } where module F = IsModuleHomomorphism f-homo; module G = IsModuleHomomorphism g-homo

  isModuleMonomorphism : IsModuleMonomorphism M₁ M₂ f →
                         IsModuleMonomorphism M₂ M₃ g →
                         IsModuleMonomorphism M₁ M₃ (g ∘ f)
  isModuleMonomorphism f-mono g-mono = record
    { isModuleHomomorphism = isModuleHomomorphism F.isModuleHomomorphism G.isModuleHomomorphism
    ; injective            = F.injective ∘ G.injective
    } where module F = IsModuleMonomorphism f-mono; module G = IsModuleMonomorphism g-mono

  isModuleIsomorphism : IsModuleIsomorphism M₁ M₂ f →
                        IsModuleIsomorphism M₂ M₃ g →
                        IsModuleIsomorphism M₁ M₃ (g ∘ f)
  isModuleIsomorphism f-iso g-iso = record
    { isModuleMonomorphism = isModuleMonomorphism F.isModuleMonomorphism G.isModuleMonomorphism
    ; surjective           = Func.surjective (_≈ᴹ_ M₁) _ _ (≈ᴹ-trans M₃) G.⟦⟧-cong F.surjective G.surjective
    } where module F = IsModuleIsomorphism f-iso; module G = IsModuleIsomorphism g-iso
