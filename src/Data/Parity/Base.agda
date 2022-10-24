------------------------------------------------------------------------
-- The Agda standard library
--
-- Parity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Parity.Base where

open import Data.Sign.Base using (Sign; +; -)

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
-- Homomorphism from Parity to Sign: here, or somewhere else?

toSign : Parity → Sign
toSign 0ℙ = +
toSign 1ℙ = -

fromSign : Sign → Parity
fromSign + = 0ℙ
fromSign - = 1ℙ
