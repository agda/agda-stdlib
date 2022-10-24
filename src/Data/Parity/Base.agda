------------------------------------------------------------------------
-- The Agda standard library
--
-- Parity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Parity.Base where

open import Algebra.Bundles
open import Data.Sign.Base using (Sign; +; -)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Definition

data Parity : Set where
  0ℙ : Parity
  1ℙ : Parity

------------------------------------------------------------------------
-- Operations

-- The opposite parity.

_ᵒ : Parity → Parity
1ℙ ᵒ = 0ℙ
0ℙ ᵒ = 1ℙ

-- Addition.

infixl 7 _+_

_+_ : Parity → Parity → Parity
0ℙ + p = p
1ℙ + p = p ᵒ

-- Multiplication.

infixl 7 _*_

_*_ : Parity → Parity → Parity
0ℙ * p = 0ℙ
1ℙ * p = p

------------------------------------------------------------------------
-- Raw Bundles

+-rawMagma : RawMagma 0ℓ 0ℓ
+-rawMagma = record { _≈_ = _≡_ ; _∙_ = _+_ }

+-0-rawMonoid : RawMonoid 0ℓ 0ℓ
+-0-rawMonoid = record { _≈_ = _≡_ ; _∙_ = _+_ ; ε = 0ℙ }

*-rawMagma : RawMagma 0ℓ 0ℓ
*-rawMagma = record { _≈_ = _≡_ ; _∙_ = _*_ }

*-1-rawMonoid : RawMonoid 0ℓ 0ℓ
*-1-rawMonoid = record { _≈_ = _≡_ ; _∙_ = _*_ ; ε = 1ℙ }

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
-- Homomorphism from Parity to Sign: here, or somewhere else?

toSign : Parity → Sign
toSign 0ℙ = +
toSign 1ℙ = -

fromSign : Sign → Parity
fromSign + = 0ℙ
fromSign - = 1ℙ
