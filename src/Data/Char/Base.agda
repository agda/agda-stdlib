------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic definitions for Characters
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Char.Base where

open import Level using (zero)
import Data.Nat.Base as ℕ
open import Function
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Re-export the type, and renamed primitives

open import Agda.Builtin.Char public using ( Char )
  renaming
  -- testing
  ( primIsLower    to isLower
  ; primIsDigit    to isDigit
  ; primIsAlpha    to isAlpha
  ; primIsSpace    to isSpace
  ; primIsAscii    to isAscii
  ; primIsLatin1   to isLatin1
  ; primIsPrint    to isPrint
  ; primIsHexDigit to isHexDigit
  -- transforming
  ; primToUpper to toUpper
  ; primToLower to toLower
  -- converting
  ; primCharToNat to toNat
  ; primNatToChar to fromNat
  )

open import Agda.Builtin.String public using ()
  renaming ( primShowChar to show )

infix 4 _≈_
_≈_ : Rel Char zero
_≈_ = _≡_ on toNat

infix 4 _<_
_<_ : Rel Char zero
_<_ = ℕ._<_ on toNat
