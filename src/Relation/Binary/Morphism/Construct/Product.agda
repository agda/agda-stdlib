------------------------------------------------------------------------
-- The Agda standard library
--
-- The projection morphisms for relational structures arising from the
-- non-dependent product construction
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Relation.Binary.Morphism.Construct.Product where

import Data.Product.Base as Product using (<_,_>; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as Pointwise
  using (Pointwise)
open import Level using (Level)
open import Relation.Binary.Bundles.Raw using (RawSetoid)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ : Level
    A : Set a
    B : Set b
    C : Set c


------------------------------------------------------------------------
-- definitions

module _ (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂) where

  private

    _≈_ = Pointwise _≈₁_ _≈₂_

  module Proj₁ where

    isRelHomomorphism : IsRelHomomorphism _≈_ _≈₁_ Product.proj₁
    isRelHomomorphism = record { cong = Product.proj₁ }


  module Proj₂ where

    isRelHomomorphism : IsRelHomomorphism _≈_ _≈₂_ Product.proj₂
    isRelHomomorphism = record { cong = Product.proj₂ }


  module Pair (_≈′_ : Rel C ℓ)  where

    isRelHomomorphism : ∀ {h k} →
                        IsRelHomomorphism _≈′_ _≈₁_ h →
                        IsRelHomomorphism _≈′_ _≈₂_ k →
                        IsRelHomomorphism _≈′_ _≈_ Product.< h , k >
    isRelHomomorphism H K = record { cong = Product.< H.cong , K.cong > }
      where
      module H = IsRelHomomorphism H
      module K = IsRelHomomorphism K


------------------------------------------------------------------------
-- package up for export

module _ {M : RawSetoid a ℓ₁} {N : RawSetoid b ℓ₂} where

  private

    module M = RawSetoid M
    module N = RawSetoid N

  proj₁ = Proj₁.isRelHomomorphism M._≈_ N._≈_
  proj₂ = Proj₂.isRelHomomorphism M._≈_ N._≈_

  module _ {P : RawSetoid c ℓ} where

    private

      module P = RawSetoid P

    <_,_> = Pair.isRelHomomorphism M._≈_ N._≈_ P._≈_

