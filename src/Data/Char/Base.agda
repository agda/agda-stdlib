------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic definitions for Characters
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Char.Base where

------------------------------------------------------------------------
-- Re-export the type, and renamed primitives

open import Agda.Builtin.Char
  using ( Char )
  renaming -- testing
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
  public

open import Agda.Builtin.String
  using ()
  renaming ( primShowChar to show )
  public
