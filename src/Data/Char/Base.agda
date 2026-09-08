------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic definitions for Characters
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Char.Base where

import Data.Nat.Base as ℕ using (_≡ᵇ_; _<_; _<ᵇ_)
open import Data.Bool.Base using (Bool; not)
open import Function.Base using (_on_)
open import Level using (Level; zero)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using()
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_)
open import Relation.Binary.Construct.Closure.Reflexive using (ReflClosure)

private
  variable
    ℓ : Level

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

------------------------------------------------------------------------
-- Equality (propositional, boolean)

infix 4 _≈_ _≉_
_≈_ : Rel Char zero
_≈_ = _≡_ on toℕ

_≉_ : Rel Char zero
_≉_ = _≢_ on toℕ

infix 4 _≈ᵇ_ _≉ᵇ_
_≈ᵇ_ : (c d : Char) → Bool
_≈ᵇ_ = ℕ._≡ᵇ_ on toℕ

_≉ᵇ_ : (c d : Char) → Bool
c ≉ᵇ d = not (c ≈ᵇ d)

------------------------------------------------------------------------
-- Case insensitive variants

case-insensitive : Rel Char ℓ → Rel Char ℓ
case-insensitive = _on toLower

infix 4 _≈ᵢ_ _≉ᵢ_
_≈ᵢ_ : Rel Char zero
_≈ᵢ_ = case-insensitive _≈_

_≉ᵢ_ : Rel Char zero
_≉ᵢ_ = case-insensitive _≉_

------------------------------------------------------------------------
-- Order (propositional, boolean)

infix 4 _<_ _<ᵇ_
_<_ : Rel Char zero
_<_ = ℕ._<_ on toℕ

_<ᵇ_ : (c d : Char) → Bool
_<ᵇ_ = ℕ._<ᵇ_ on toℕ

infix 4 _≤_
_≤_ : Rel Char zero
_≤_ = ReflClosure _<_
