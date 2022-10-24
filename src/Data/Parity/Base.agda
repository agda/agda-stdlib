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

opposite : Parity → Parity
opposite 1ℙ = 0ℙ
opposite 0ℙ = 1ℙ

-- Addition.

infixl 7 _+_

_+_ : Parity → Parity → Parity
0ℙ + p = p
1ℙ + p = opposite p

-- Multiplication.

infixl 7 _*_

_*_ : Parity → Parity → Parity
0ℙ * p = 0ℙ
1ℙ * p = p

------------------------------------------------------------------------
-- Homomorphism from Parity to Sign: here, or somewhere else?

ℙto𝕊 : Parity → Sign
ℙto𝕊 0ℙ = +
ℙto𝕊 1ℙ = -

𝕊toℙ : Sign → Parity
𝕊toℙ + = 0ℙ
𝕊toℙ - = 1ℙ
