------------------------------------------------------------------------
-- The Agda standard library
--
-- Parity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Parity.Base where

open import Data.Sign.Base as Sign using (Sign; +; -)

------------------------------------------------------------------------
-- Definition

data Parity : Set where
  eve : Parity
  odd : Parity

pattern 0ₚ = eve
pattern 1ₚ = odd

------------------------------------------------------------------------
-- Operations

-- The opposite parity.

opposite : Parity → Parity
opposite 1ₚ = 0ₚ
opposite 0ₚ = 1ₚ

-- Addition.

infixl 7 _+_

_+_ : Parity → Parity → Parity
0ₚ + p = p
1ₚ + p = opposite p

-- Multiplication.

infixl 7 _*_

_*_ : Parity → Parity → Parity
0ₚ * p = 0ₚ
1ₚ * p = p

-- Homomorphism from Parity to Sign

homoₚₛ : Parity → Sign
homoₚₛ 0ₚ = +
homoₚₛ 1ₚ = -
