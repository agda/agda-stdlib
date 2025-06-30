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
import Relation.Binary.Morphism.Construct.Product as RP

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
      { isRelHomomorphism = RP.proj₁
      ; homo              = λ _ _ → refl
      }

  module Proj₂ (refl : Reflexive N._≈_) where

    isMagmaHomomorphism : IsMagmaHomomorphism (rawMagma M N) N Product.proj₂
    isMagmaHomomorphism = record
      { isRelHomomorphism = RP.proj₂
      ; homo              = λ _ _ → refl
      }

  module Pair (P : RawMagma c ℓ₃) where

    isMagmaHomomorphism : ∀ {f g} →
                          IsMagmaHomomorphism P M f →
                          IsMagmaHomomorphism P N g →
                          IsMagmaHomomorphism P (rawMagma M N) (Product.< f , g >)
    isMagmaHomomorphism F G = record
      { isRelHomomorphism = RP.< F.isRelHomomorphism , G.isRelHomomorphism >
      ; homo              = λ x y → F.homo x y , G.homo x y
      }
      where
        module F = IsMagmaHomomorphism F
        module G = IsMagmaHomomorphism G

-- Package for export
module Magma-Export {M : RawMagma a ℓ₁} {N : RawMagma b ℓ₂} where
  open Magma

  private
    module M = RawMagma M
    module N = RawMagma N

  module _ {refl : Reflexive M._≈_} where
    proj₁ = Proj₁.isMagmaHomomorphism M M refl

  module _ {refl : Reflexive N._≈_} where
    proj₂ = Proj₂.isMagmaHomomorphism M N refl

  module _ {P : RawMagma c ℓ₃} where
    <_,_> = Pair.isMagmaHomomorphism M N P

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

    isMonoidHomomorphism : ∀ {f g} →
                          IsMonoidHomomorphism P M f →
                          IsMonoidHomomorphism P N g →
                          IsMonoidHomomorphism P (rawMonoid M N) (Product.< f , g >)
    isMonoidHomomorphism F G = record
      { isMagmaHomomorphism = Magma.Pair.isMagmaHomomorphism M.rawMagma N.rawMagma P.rawMagma F.isMagmaHomomorphism G.isMagmaHomomorphism
      ; ε-homo              = F.ε-homo , G.ε-homo }
      where
        module F = IsMonoidHomomorphism F
        module G = IsMonoidHomomorphism G

-- Package for export
module Monoid-Export {M : RawMonoid a ℓ₁} {N : RawMonoid b ℓ₂} where
  open Monoid

  private
    module M = RawMonoid M
    module N = RawMonoid N

  module _ {refl : Reflexive M._≈_} where
    proj₁ = Proj₁.isMonoidHomomorphism M M refl

  module _ {refl : Reflexive N._≈_} where
    proj₂ = Proj₂.isMonoidHomomorphism M N refl

  module _ {P : RawMonoid c ℓ₃} where
    <_,_> = Pair.isMonoidHomomorphism M N P
