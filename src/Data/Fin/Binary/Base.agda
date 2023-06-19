------------------------------------------------------------------------
-- The Agda standard library
--
-- A binary representation of finite sets
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible #-}

module Data.Fin.Binary.Base where

open import Data.Nat.Binary.Base as ℕᵇ hiding (zero; suc)

private
  variable
    n : ℕᵇ

data Finᵇ : ℕᵇ → Set where
  zeroᵒ   : Finᵇ 1+[2 n ]
  zeroᵉ   : Finᵇ 2[1+ n ]
  oneᵉ    : Finᵇ 2[1+ n ]
  1+[2_]ᵒ : Finᵇ n → Finᵇ 1+[2 n ]
  2[1+_]ᵒ : Finᵇ n → Finᵇ 1+[2 n ]
  2[1+_]ᵉ : Finᵇ n → Finᵇ 2[1+ n ]
  3+[2_]ᵉ : Finᵇ n → Finᵇ 2[1+ n ]

zero : Finᵇ (ℕᵇ.suc n)
zero {n = ℕᵇ.zero} = zeroᵒ
zero {n = 2[1+ n ]} = zeroᵒ
zero {n = 1+[2 n ]} = zeroᵉ

suc : Finᵇ n → Finᵇ (ℕᵇ.suc n)
suc zeroᵒ = oneᵉ
suc zeroᵉ = 1+[2 zero ]ᵒ
suc oneᵉ = 2[1+ zero ]ᵒ
suc 1+[2 i ]ᵒ = 2[1+ i ]ᵉ
suc 2[1+ i ]ᵒ = 3+[2 i ]ᵉ
suc 2[1+ i ]ᵉ = 1+[2 suc i ]ᵒ
suc 3+[2 i ]ᵉ = 2[1+ suc i ]ᵒ
