------------------------------------------------------------------------
-- The Agda standard library
--
-- Parity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Parity.Base where

open import Data.Sign.Base as Sign using (Sign) renaming (+ to 0𝕊; - to 1𝕊)

------------------------------------------------------------------------
-- Definition

data Parity : Set where
  eve : Parity
  odd : Parity

pattern 0ℙ = eve
pattern 1ℙ = odd

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

-- Homomorphism from Parity to Sign

ℙto𝕊 : Parity → Sign
ℙto𝕊 0ℙ = 0𝕊
ℙto𝕊 1ℙ = 1𝕊

𝕊toℙ : Sign → Parity
𝕊toℙ 0𝕊 = 0ℙ
𝕊toℙ 1𝕊 = 1ℙ
