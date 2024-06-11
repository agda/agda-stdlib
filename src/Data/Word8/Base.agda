------------------------------------------------------------------------
-- The Agda standard library
--
-- Bytes: base type and functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Data.Word8.Base where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Nat using (Nat; _==_)
open import Agda.Builtin.Unit using (⊤)

open import Data.Fin.Base as Fin using (Fin)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)

open import Function.Base using (_$_; _|>_)

------------------------------------------------------------------------------
-- Re-export type and operations

open import Data.Word8.Primitive as Prim public
  using ( Word8
        ; _+_
        ; show
        )
  renaming ( fromNat to fromℕ
           ; toNat to toℕ
           )

testBit : Word8 → Fin 8 → Bool
testBit w i = Prim.testBit w (Fin.toℕ i)

_[_]≔_ : Word8 → Fin 8 → Bool → Word8
w [ i ]≔ false = Prim.clearBit w (Fin.toℕ i)
w [ i ]≔ true  = Prim.setBit w (Fin.toℕ i)

------------------------------------------------------------------------------
-- Basic functions

toBits : Word8 → Vec Bool 8
toBits w = Vec.tabulate (testBit w)

fromBits : Vec Bool 8 → Word8
fromBits bs = Vec.foldl′ _|>_ (fromℕ 0)
            $ Vec.zipWith (λ i b → _[ i ]≔ b) (Vec.allFin 8) bs

_≡ᵇ_ : Word8 → Word8 → Bool
w ≡ᵇ w′ = toℕ w == toℕ w′
