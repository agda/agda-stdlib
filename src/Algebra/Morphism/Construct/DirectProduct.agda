------------------------------------------------------------------------
-- The Agda standard library
--
-- The projection morphisms for alegraic structures arising from the
-- direct product construction
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Algebra.Morphism.Construct.DirectProduct where

open import Algebra.Bundles
open import Algebra.Morphism.Structures
  using ( module MagmaMorphisms
        ; module MonoidMorphisms
        )
open import Data.Product
open import Level using (Level)
open import Relation.Binary.Definitions using (Reflexive)
open import Algebra.Construct.DirectProduct

private
  variable
    c ℓ : Level

------------------------------------------------------------------------
-- Magmas

module _ (M N : RawMagma c ℓ) (open RawMagma M) (refl : Reflexive _≈_) where
  open MagmaMorphisms (rawMagma M N) M

  isMagmaHomomorphism-proj₁ : IsMagmaHomomorphism proj₁
  isMagmaHomomorphism-proj₁ = record
    { isRelHomomorphism = record { cong = λ {x} {y} z → z .proj₁ }
    ; homo              = λ _ _ → refl
    }

module _ (M N : RawMagma c ℓ) (open RawMagma N) (refl : Reflexive _≈_) where
  open MagmaMorphisms (rawMagma M N) N

  isMagmaHomomorphism-proj₂ : IsMagmaHomomorphism proj₂
  isMagmaHomomorphism-proj₂ = record
    { isRelHomomorphism = record { cong = λ {x} {y} z → z .proj₂ }
    ; homo              = λ _ _ → refl
    }

------------------------------------------------------------------------
-- Monoids

module _ (M N : RawMonoid c ℓ) (open RawMonoid M) (refl : Reflexive _≈_) where
  open MonoidMorphisms (rawMonoid M N) M

  isMonoidHomomorphism-proj₁ : IsMonoidHomomorphism proj₁
  isMonoidHomomorphism-proj₁ = record
    { isMagmaHomomorphism = isMagmaHomomorphism-proj₁ _ _ refl
    ; ε-homo = refl
    }

module _ (M N : RawMonoid c ℓ) (open RawMonoid N) (refl : Reflexive _≈_) where
  open MonoidMorphisms (rawMonoid M N) N

  isMonoidHomomorphism-proj₂ : IsMonoidHomomorphism proj₂
  isMonoidHomomorphism-proj₂ = record
    { isMagmaHomomorphism = isMagmaHomomorphism-proj₂ _ _ refl
    ; ε-homo = refl
    }
