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
import Data.Nat.Show as ℕ
open import Data.String using (_++_; fromVec; padLeft)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Word8.Base
open import Function.Base using (_$_)

showBits : Word8 → String
showBits w
  = "0b" ++_
  $ fromVec
  $ Vec.reverse
  $ Vec.map showBit
  $ toBits w

showHexa : Word8 → String
showHexa w
  = "0x" ++_
  $ padLeft '0' 2
  $ ℕ.showInBase 16 (toℕ w)
