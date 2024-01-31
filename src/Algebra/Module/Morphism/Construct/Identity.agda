------------------------------------------------------------------------
-- The Agda standard library
--
-- The identity morphism for module-like algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Algebra.Module.Morphism.Construct.Identity where

open import Algebra.Module.Bundles.Raw
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
import Function.Construct.Identity as Id
open import Level using (Level)
open import Relation.Binary.Definitions using (Reflexive)

private
  variable
    r s m ℓm : Level

module _ {R : Set r} (M : RawLeftSemimodule R m ℓm) (open RawLeftSemimodule M) (≈ᴹ-refl : Reflexive _≈ᴹ_) where
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
    ; surjective                   = Id.surjective _
    }

module _ {R : Set r} (M : RawLeftModule R m ℓm) (open RawLeftModule M) (≈ᴹ-refl : Reflexive _≈ᴹ_)  where
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
    ; surjective               = Id.surjective _
    }

module _ {R : Set r} (M : RawRightSemimodule R m ℓm) (open RawRightSemimodule M) (≈ᴹ-refl : Reflexive _≈ᴹ_) where
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
    ; surjective                    = Id.surjective _
    }

module _ {R : Set r} (M : RawRightModule R m ℓm) (open RawRightModule M) (≈ᴹ-refl : Reflexive _≈ᴹ_) where
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
    ; surjective                = Id.surjective _
    }

module _ {R : Set r} {S : Set s} (M : RawBisemimodule R S m ℓm) (open RawBisemimodule M) (≈ᴹ-refl : Reflexive _≈ᴹ_) where
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
    ; surjective                 = Id.surjective _
    }

module _ {R : Set r} {S : Set s} (M : RawBimodule R S m ℓm) (open RawBimodule M) (≈ᴹ-refl : Reflexive _≈ᴹ_) where
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
    ; surjective             = Id.surjective _
    }

module _ {R : Set r} (M : RawSemimodule R m ℓm) (open RawSemimodule M) (≈ᴹ-refl : Reflexive _≈ᴹ_)  where
  open SemimoduleMorphisms M M

  isSemimoduleHomomorphism : IsSemimoduleHomomorphism id
  isSemimoduleHomomorphism = record
    { isBisemimoduleHomomorphism = isBisemimoduleHomomorphism _ ≈ᴹ-refl
    }

  isSemimoduleMonomorphism : IsSemimoduleMonomorphism id
  isSemimoduleMonomorphism = record
    { isSemimoduleHomomorphism = isSemimoduleHomomorphism
    ; injective                = id
    }

  isSemimoduleIsomorphism : IsSemimoduleIsomorphism id
  isSemimoduleIsomorphism = record
    { isSemimoduleMonomorphism = isSemimoduleMonomorphism
    ; surjective               = Id.surjective _
    }

module _ {R : Set r} (M : RawModule R m ℓm) (open RawModule M) (≈ᴹ-refl : Reflexive _≈ᴹ_) where
  open ModuleMorphisms M M

  isModuleHomomorphism : IsModuleHomomorphism id
  isModuleHomomorphism = record
    { isBimoduleHomomorphism = isBimoduleHomomorphism _ ≈ᴹ-refl
    }

  isModuleMonomorphism : IsModuleMonomorphism id
  isModuleMonomorphism = record
    { isModuleHomomorphism = isModuleHomomorphism
    ; injective            = id
    }

  isModuleIsomorphism : IsModuleIsomorphism id
  isModuleIsomorphism = record
    { isModuleMonomorphism = isModuleMonomorphism
    ; surjective           = Id.surjective _
    }
