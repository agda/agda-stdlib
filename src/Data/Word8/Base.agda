------------------------------------------------------------------------
-- The Agda standard library
--
-- Bytes: base type and functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Data.Word8.Base where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; _==_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)

------------------------------------------------------------------------------
-- Re-export type and operations

open import Data.Word8.Primitive as Prim public
  using ( Word8
        ; _+_)
  renaming ( fromNat to fromℕ
           ; toNat to toℕ
           )

------------------------------------------------------------------------------
-- Basic functions

_≡ᵇ_ : Word8 → Word8 → Bool
w ≡ᵇ w′ = toℕ w == toℕ w′
