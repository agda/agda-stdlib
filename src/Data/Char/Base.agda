------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic definitions for Characters
------------------------------------------------------------------------
module Data.Char.Base where

open import Agda.Builtin.String using (primShowChar)
open import Data.Nat.Base    using (ℕ)
open import Data.Bool.Base   using (Bool)
open import Data.String.Base using (String)

------------------------------------------------------------------------
-- Re-export the type

import Agda.Builtin.Char as AgdaChar
open AgdaChar using (Char) public

------------------------------------------------------------------------
-- Primitive operations

open AgdaChar

show : Char → String
show = primShowChar

isLower : Char → Bool
isLower = primIsLower

isDigit : Char → Bool
isDigit = primIsDigit

isAlpha : Char → Bool
isAlpha = primIsAlpha

isSpace : Char → Bool
isSpace = primIsSpace

isAscii : Char → Bool
isAscii = primIsAscii

isLatin1 : Char → Bool
isLatin1 = primIsLatin1

isPrint : Char → Bool
isPrint = primIsPrint

isHexDigit : Char → Bool
isHexDigit = primIsHexDigit

toNat : Char → ℕ
toNat = primCharToNat

fromNat : ℕ → Char
fromNat = primNatToChar
