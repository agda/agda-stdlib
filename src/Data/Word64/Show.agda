------------------------------------------------------------------------
-- The Agda standard library
--
-- Bytes: showing bit patterns
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Data.Word64.Show where

open import Agda.Builtin.String using (String)

open import Data.Bool.Show using (showBit)
open import Data.Fin.Base as Fin using (Fin)
import Data.Nat.Show as ℕ using (showInBase)
open import Data.String using (_++_; fromVec; padLeft; String)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Word64.Base using (Word64; toℕ)
open import Data.Word64.Unsafe using (toBits)

open import Data.Bool
open import Data.Nat
open import Data.List using ( List )
open import Data.String
open import Data.Word64

open import Data.Digit using ( toNatDigits )
open import Data.Char as Char
open import Function.Base using ( _$_ ; _∘′_ )

showBits : Word64 → String
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
toHexadecimalChars = Data.List.map toHexDigitChar ∘′ toNatDigits 16

showHexa : Word64 -> String
showHexa w = "0x" ++_
  $ padLeft '0' 16
  $ Data.String.fromList
  $ toHexadecimalChars (Data.Word64.toℕ w)

