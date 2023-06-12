------------------------------------------------------------------------
-- The Agda standard library
--
-- A binary representation of finite sets
------------------------------------------------------------------------
{-# OPTIONS --safe --cubical-compatible #-}

module Data.Fin.Binary.Base where

open import Data.Nat.Binary.Base

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
  3+[2_]ᵒ : Finᵇ n → Finᵇ 2[1+ n ]
