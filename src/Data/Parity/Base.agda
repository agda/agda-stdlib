------------------------------------------------------------------------
-- The Agda standard library
--
-- Parity
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Parity.Base where

open import Algebra.Bundles.Raw
  using (RawMagma; RawMonoid; RawGroup; RawNearSemiring; RawSemiring)
open import Data.Sign.Base using (Sign; +; -)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

------------------------------------------------------------------------
-- Definition

data Parity : Set where
  0ℙ : Parity
  1ℙ : Parity

------------------------------------------------------------------------
-- Operations

-- The opposite parity.

infix 8 _⁻¹

_⁻¹ : Parity → Parity
1ℙ ⁻¹ = 0ℙ
0ℙ ⁻¹ = 1ℙ

-- Addition.

infixl 7 _+_

_+_ : Parity → Parity → Parity
0ℙ + p = p
1ℙ + p = p ⁻¹

-- Multiplication.

infixl 7 _*_

_*_ : Parity → Parity → Parity
0ℙ * p = 0ℙ
1ℙ * p = p

------------------------------------------------------------------------
-- Raw Bundles

+-rawMagma : RawMagma 0ℓ 0ℓ
+-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  }

+-0-rawMonoid : RawMonoid 0ℓ 0ℓ
+-0-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  ; ε = 0ℙ
  }

+-0-rawGroup : RawGroup 0ℓ 0ℓ
+-0-rawGroup = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  ; _⁻¹ = _⁻¹
  ; ε = 0ℙ
  }

*-rawMagma : RawMagma 0ℓ 0ℓ
*-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  }

*-1-rawMonoid : RawMonoid 0ℓ 0ℓ
*-1-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  ; ε = 1ℙ
  }

+-*-rawNearSemiring : RawNearSemiring 0ℓ 0ℓ
+-*-rawNearSemiring = record
  { Carrier = _
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = 0ℙ
  }

+-*-rawSemiring : RawSemiring 0ℓ 0ℓ
+-*-rawSemiring = record
  { Carrier = _
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = 0ℙ
  ; 1# = 1ℙ
  }


------------------------------------------------------------------------
-- Homomorphisms between Parity and Sign

toSign : Parity → Sign
toSign 0ℙ = +
toSign 1ℙ = -

fromSign : Sign → Parity
fromSign + = 0ℙ
fromSign - = 1ℙ
