------------------------------------------------------------------------
-- The Agda standard library
--
-- The projection morphisms for relational structures arising from the
-- product construction
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Relation.Binary.Morphism.Construct.Product where

import Data.Product.Base as Product using (<_,_>; proj₁; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as Pointwise
  using (Pointwise)
open import Level using (Level)
--open import Relation.Binary.Construct using ()
open import Relation.Binary.Bundles.Raw using (RawSetoid)
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)

private
  variable
    a b c ℓ₁ ℓ₂ ℓ : Level


------------------------------------------------------------------------
-- product construction on RawSetoid belongs in Relation.Binary.Construct.Product?

module _ (M : RawSetoid a ℓ₁) (N : RawSetoid b ℓ₂) where

  private

    module M = RawSetoid M
    module N = RawSetoid N

    P : RawSetoid _ _
    P = record { _≈_ = Pointwise M._≈_ N._≈_ }

    module P = RawSetoid P

  module Proj₁ where

    isRelHomomorphism : IsRelHomomorphism P._≈_ M._≈_ Product.proj₁
    isRelHomomorphism = record { cong = λ z → z .Product.proj₁ }


  module Proj₂ where

    isRelHomomorphism : IsRelHomomorphism P._≈_ N._≈_ Product.proj₂
    isRelHomomorphism = record { cong = λ z → z .Product.proj₂ }


  module Pair (X : RawSetoid c ℓ)  where

    private module X = RawSetoid X

    isRelHomomorphism : ∀ {h k} →
                        IsRelHomomorphism X._≈_ M._≈_ h →
                        IsRelHomomorphism X._≈_ N._≈_ k →
                        IsRelHomomorphism X._≈_ P._≈_ Product.< h , k >
    isRelHomomorphism H K = record { cong = Product.< H.cong , K.cong > }
      where
      module H = IsRelHomomorphism H
      module K = IsRelHomomorphism K


------------------------------------------------------------------------
-- package up for export

module _ {M : RawSetoid a ℓ₁} {N : RawSetoid b ℓ₂} where

  proj₁ = Proj₁.isRelHomomorphism M N
  proj₂ = Proj₂.isRelHomomorphism M N

module _ {M : RawSetoid a ℓ₁} {N : RawSetoid b ℓ₂} {P : RawSetoid c ℓ} where

  <_,_> = Pair.isRelHomomorphism M N P

