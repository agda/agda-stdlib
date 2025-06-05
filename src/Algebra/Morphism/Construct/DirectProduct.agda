------------------------------------------------------------------------
-- The Agda standard library
--
-- The projection morphisms for algebraic structures arising from the
-- direct product construction
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Algebra.Morphism.Construct.DirectProduct where

open import Algebra.Bundles using (RawMagma; RawMonoid)
open import Algebra.Construct.DirectProduct using (rawMagma; rawMonoid)
open import Algebra.Morphism.Structures
  using ( module MagmaMorphisms
        ; module MonoidMorphisms
        )
open import Data.Product as Product
  using (_,_)
open import Level using (Level)
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Binary.Morphism.Construct.Product
  using (proj₁; proj₂; <_,_>)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

------------------------------------------------------------------------
-- Magmas

module Magma (M : RawMagma a ℓ₁) (N : RawMagma b ℓ₂) where
  open MagmaMorphisms

  private
    module M = RawMagma M
    module N = RawMagma N

  module Proj₁ (refl : Reflexive M._≈_) where

    isMagmaHomomorphism : IsMagmaHomomorphism (rawMagma M N) M Product.proj₁
    isMagmaHomomorphism = record
      { isRelHomomorphism = proj₁
      ; homo              = λ _ _ → refl
      }

  module Proj₂ (refl : Reflexive N._≈_) where

    isMagmaHomomorphism : IsMagmaHomomorphism (rawMagma M N) N Product.proj₂
    isMagmaHomomorphism = record
      { isRelHomomorphism = proj₂
      ; homo              = λ _ _ → refl
      }

  module Pair (P : RawMagma c ℓ₃) where

    isMagmaHomomorphism : ∀ {f h} →
                          IsMagmaHomomorphism P M f →
                          IsMagmaHomomorphism P N h →
                          IsMagmaHomomorphism P (rawMagma M N) (Product.< f , h >)
    isMagmaHomomorphism F H = record
      { isRelHomomorphism = < F.isRelHomomorphism , H.isRelHomomorphism >
      ; homo              = λ x y → F.homo x y , H.homo x y
      }
      where
        module F = IsMagmaHomomorphism F
        module H = IsMagmaHomomorphism H

------------------------------------------------------------------------
-- Monoids

module Monoid (M : RawMonoid a ℓ₁) (N : RawMonoid b ℓ₂) where
  open MonoidMorphisms

  private
    module M = RawMonoid M
    module N = RawMonoid N

  module Proj₁ (refl : Reflexive M._≈_) where

    isMonoidHomomorphism : IsMonoidHomomorphism (rawMonoid M N) M Product.proj₁
    isMonoidHomomorphism = record
      { isMagmaHomomorphism = Magma.Proj₁.isMagmaHomomorphism M.rawMagma N.rawMagma refl
      ; ε-homo              = refl
      }

  module Proj₂ (refl : Reflexive N._≈_) where

    isMonoidHomomorphism : IsMonoidHomomorphism (rawMonoid M N) N Product.proj₂
    isMonoidHomomorphism = record
      { isMagmaHomomorphism = Magma.Proj₂.isMagmaHomomorphism M.rawMagma N.rawMagma refl
      ; ε-homo              = refl
      }

  module Pair (P : RawMonoid c ℓ₃) where

    private
      module P = RawMonoid P

    isMonoidHomomorphism : ∀ {f h} →
                          IsMonoidHomomorphism P M f →
                          IsMonoidHomomorphism P N h →
                          IsMonoidHomomorphism P (rawMonoid M N) (Product.< f , h >)
    isMonoidHomomorphism F H = record
      { isMagmaHomomorphism = Magma.Pair.isMagmaHomomorphism M.rawMagma N.rawMagma P.rawMagma F.isMagmaHomomorphism H.isMagmaHomomorphism
      ; ε-homo              = F.ε-homo , H.ε-homo }
      where
        module F = IsMonoidHomomorphism F
        module H = IsMonoidHomomorphism H
