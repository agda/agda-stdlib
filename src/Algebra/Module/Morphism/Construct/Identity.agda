------------------------------------------------------------------------
-- The Agda standard library
--
-- The identity morphism for module-like algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Algebra.Module.Morphism.Construct.Identity where

open import Algebra.Bundles
open import Algebra.Module.Bundles
open import Algebra.Module.Morphism.Structures
  using ( module LeftSemimoduleMorphisms
        ; module LeftModuleMorphisms
        ; module RightSemimoduleMorphisms
        ; module RightModuleMorphisms
        ; module BisemimoduleMorphisms
        ; module BimoduleMorphisms
        ; module SemimoduleMorphisms
        ; module ModuleMorphisms
        )
open import Algebra.Morphism.Construct.Identity
open import Data.Product.Base using (_,_)
open import Function.Base using (id)
open import Level using (Level)

private
  variable
    r ℓr s ℓs m ℓm : Level

module _ {semiring : Semiring r ℓr} (M : LeftSemimodule semiring m ℓm) where
  open LeftSemimodule M using (≈ᴹ-refl)
  open LeftSemimoduleMorphisms M M

  isLeftSemimoduleHomomorphism : IsLeftSemimoduleHomomorphism id
  isLeftSemimoduleHomomorphism = record
    { +ᴹ-isMonoidHomomorphism = isMonoidHomomorphism _ ≈ᴹ-refl
    ; *ₗ-homo                 = λ _ _ → ≈ᴹ-refl
    }

  isLeftSemimoduleMonomorphism : IsLeftSemimoduleMonomorphism id
  isLeftSemimoduleMonomorphism = record
    { isLeftSemimoduleHomomorphism = isLeftSemimoduleHomomorphism
    ; injective                    = id
    }

  isLeftSemimoduleIsomorphism : IsLeftSemimoduleIsomorphism id
  isLeftSemimoduleIsomorphism = record
    { isLeftSemimoduleMonomorphism = isLeftSemimoduleMonomorphism
    ; surjective                   = _, ≈ᴹ-refl
    }

module _ {ring : Ring r ℓr} (M : LeftModule ring m ℓm) where
  open LeftModule M using (≈ᴹ-refl)
  open LeftModuleMorphisms M M

  isLeftModuleHomomorphism : IsLeftModuleHomomorphism id
  isLeftModuleHomomorphism = record
    { +ᴹ-isGroupHomomorphism = isGroupHomomorphism _ ≈ᴹ-refl
    ; *ₗ-homo                = λ _ _ → ≈ᴹ-refl
    }

  isLeftModuleMonomorphism : IsLeftModuleMonomorphism id
  isLeftModuleMonomorphism = record
    { isLeftModuleHomomorphism = isLeftModuleHomomorphism
    ; injective                = id
    }

  isLeftModuleIsomorphism : IsLeftModuleIsomorphism id
  isLeftModuleIsomorphism = record
    { isLeftModuleMonomorphism = isLeftModuleMonomorphism
    ; surjective               = _, ≈ᴹ-refl
    }

module _ {semiring : Semiring r ℓr} (M : RightSemimodule semiring m ℓm) where
  open RightSemimodule M using (≈ᴹ-refl)
  open RightSemimoduleMorphisms M M

  isRightSemimoduleHomomorphism : IsRightSemimoduleHomomorphism id
  isRightSemimoduleHomomorphism = record
    { +ᴹ-isMonoidHomomorphism = isMonoidHomomorphism _ ≈ᴹ-refl
    ; *ᵣ-homo                 = λ _ _ → ≈ᴹ-refl
    }

  isRightSemimoduleMonomorphism : IsRightSemimoduleMonomorphism id
  isRightSemimoduleMonomorphism = record
    { isRightSemimoduleHomomorphism = isRightSemimoduleHomomorphism
    ; injective                   = id
    }

  isRightSemimoduleIsomorphism : IsRightSemimoduleIsomorphism id
  isRightSemimoduleIsomorphism = record
    { isRightSemimoduleMonomorphism = isRightSemimoduleMonomorphism
    ; surjective                    = _, ≈ᴹ-refl
    }

module _ {ring : Ring r ℓr} (M : RightModule ring m ℓm) where
  open RightModule M using (≈ᴹ-refl)
  open RightModuleMorphisms M M

  isRightModuleHomomorphism : IsRightModuleHomomorphism id
  isRightModuleHomomorphism = record
    { +ᴹ-isGroupHomomorphism = isGroupHomomorphism _ ≈ᴹ-refl
    ; *ᵣ-homo                = λ _ _ → ≈ᴹ-refl
    }

  isRightModuleMonomorphism : IsRightModuleMonomorphism id
  isRightModuleMonomorphism = record
    { isRightModuleHomomorphism = isRightModuleHomomorphism
    ; injective                 = id
    }

  isRightModuleIsomorphism : IsRightModuleIsomorphism id
  isRightModuleIsomorphism = record
    { isRightModuleMonomorphism = isRightModuleMonomorphism
    ; surjective                = _, ≈ᴹ-refl
    }

module _ {R-semiring : Semiring r ℓr} {S-semiring : Semiring s ℓs} (M : Bisemimodule R-semiring S-semiring m ℓm) where
  open Bisemimodule M using (≈ᴹ-refl)
  open BisemimoduleMorphisms M M

  isBisemimoduleHomomorphism : IsBisemimoduleHomomorphism id
  isBisemimoduleHomomorphism = record
    { +ᴹ-isMonoidHomomorphism = isMonoidHomomorphism _ ≈ᴹ-refl
    ; *ₗ-homo                 = λ _ _ → ≈ᴹ-refl
    ; *ᵣ-homo                 = λ _ _ → ≈ᴹ-refl
    }

  isBisemimoduleMonomorphism : IsBisemimoduleMonomorphism id
  isBisemimoduleMonomorphism = record
    { isBisemimoduleHomomorphism = isBisemimoduleHomomorphism
    ; injective                  = id
    }

  isBisemimoduleIsomorphism : IsBisemimoduleIsomorphism id
  isBisemimoduleIsomorphism = record
    { isBisemimoduleMonomorphism = isBisemimoduleMonomorphism
    ; surjective                 = _, ≈ᴹ-refl
    }

module _ {R-ring : Ring r ℓr} {S-ring : Ring r ℓr} (M : Bimodule R-ring S-ring m ℓm) where
  open Bimodule M using (≈ᴹ-refl)
  open BimoduleMorphisms M M

  isBimoduleHomomorphism : IsBimoduleHomomorphism id
  isBimoduleHomomorphism = record
    { +ᴹ-isGroupHomomorphism = isGroupHomomorphism _ ≈ᴹ-refl
    ; *ₗ-homo                = λ _ _ → ≈ᴹ-refl
    ; *ᵣ-homo                = λ _ _ → ≈ᴹ-refl
    }

  isBimoduleMonomorphism : IsBimoduleMonomorphism id
  isBimoduleMonomorphism = record
    { isBimoduleHomomorphism = isBimoduleHomomorphism
    ; injective              = id
    }

  isBimoduleIsomorphism : IsBimoduleIsomorphism id
  isBimoduleIsomorphism = record
    { isBimoduleMonomorphism = isBimoduleMonomorphism
    ; surjective             = _, ≈ᴹ-refl
    }

module _ {commutativeSemiring : CommutativeSemiring r ℓr} (M : Semimodule commutativeSemiring m ℓm) where
  open Semimodule M using (≈ᴹ-refl)
  open SemimoduleMorphisms M M

  isSemimoduleHomomorphism : IsSemimoduleHomomorphism id
  isSemimoduleHomomorphism = record
    { isBisemimoduleHomomorphism = isBisemimoduleHomomorphism _
    }

  isSemimoduleMonomorphism : IsSemimoduleMonomorphism id
  isSemimoduleMonomorphism = record
    { isSemimoduleHomomorphism = isSemimoduleHomomorphism
    ; injective                = id
    }

  isSemimoduleIsomorphism : IsSemimoduleIsomorphism id
  isSemimoduleIsomorphism = record
    { isSemimoduleMonomorphism = isSemimoduleMonomorphism
    ; surjective               = _, ≈ᴹ-refl
    }

module _ {commutativeRing : CommutativeRing r ℓr} (M : Module commutativeRing m ℓm) where
  open Module M using (≈ᴹ-refl)
  open ModuleMorphisms M M

  isModuleHomomorphism : IsModuleHomomorphism id
  isModuleHomomorphism = record
    { isBimoduleHomomorphism = isBimoduleHomomorphism _
    }

  isModuleMonomorphism : IsModuleMonomorphism id
  isModuleMonomorphism = record
    { isModuleHomomorphism = isModuleHomomorphism
    ; injective            = id
    }

  isModuleIsomorphism : IsModuleIsomorphism id
  isModuleIsomorphism = record
    { isModuleMonomorphism = isModuleMonomorphism
    ; surjective           = _, ≈ᴹ-refl
    }
