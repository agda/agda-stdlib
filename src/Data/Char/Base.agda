------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic definitions for Characters
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Char.Base where

open import Level using (zero)
import Data.Nat.Base as ℕ
open import Data.Bool.Base using (Bool)
open import Function.Base using (_on_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.Construct.Closure.Reflexive

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
  ; primCharToNat to toℕ
  ; primNatToChar to fromℕ
  )

open import Agda.Builtin.String public using ()
  renaming ( primShowChar to show )

infix 4 _≈_ _≉_
_≈_ : Rel Char zero
_≈_ = _≡_ on toℕ

_≉_ : Rel Char zero
_≉_ = _≢_ on toℕ

infix 4 _≈ᵇ_
_≈ᵇ_ : (c d : Char) → Bool
c ≈ᵇ d = toℕ c ℕ.≡ᵇ toℕ d

infix 4 _<_
_<_ : Rel Char zero
_<_ = ℕ._<_ on toℕ

infix 4 _≤_
_≤_ : Rel Char zero
_≤_ = ReflClosure _<_

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

toNat = toℕ
{-# WARNING_ON_USAGE toNat
"Warning: toNat was deprecated in v1.1.
Please use toℕ instead."
#-}

fromNat = fromℕ
{-# WARNING_ON_USAGE fromNat
"Warning: fromNat was deprecated in v1.1.
Please use fromℕ instead."
#-}
