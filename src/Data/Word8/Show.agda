------------------------------------------------------------------------
-- The Agda standard library
--
-- Bytes: showing bit patterns
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Data.Word8.Show where

open import Agda.Builtin.String using (String)
open import Data.Bool.Show using (showBit)
open import Data.Fin.Base as Fin using (Fin)
import Data.Nat.Show as ℕ using (showInBase)
open import Data.String using (_++_; fromVec; padLeft; fromList)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Word8.Base using (Word8; toℕ; toBits)
open import Function.Base using (_$_; _∘′_)
open import Data.Digit using (toNatDigits)
open import Data.List using (List; map)
open import Data.Char as Char
open import Data.Bool.Base using (if_then_else_)
open import Data.Nat


showBits : Word8 → String
showBits w
  = "0b" ++_
  $ fromVec
  $ Vec.reverse
  $ Vec.map showBit
  $ toBits w

toHexDigitChar : ℕ → Char
toHexDigitChar n = if n <ᵇ 10
  then Char.fromℕ (n + Char.toℕ '0')
  else Char.fromℕ (n ∸ 10 + Char.toℕ 'a')

toHexadecimalChars : ℕ → List Char
toHexadecimalChars = map toHexDigitChar ∘′ toNatDigits 16

showHexa : Word8 → String
showHexa w = "0x" ++_
  $ padLeft '0' 2
  $ fromList
  $ toHexadecimalChars (Data.Word8.Base.toℕ w)
