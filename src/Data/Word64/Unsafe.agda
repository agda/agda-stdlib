------------------------------------------------------------------------
-- The Agda standard library
--
-- Machine words: unsafe functions using the FFI
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Data.Word64.Unsafe where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Product.Base using (proj₁)
open import Data.Vec.Base as Vec using (Vec)
open import Data.Word8.Base as Word8 using (Word8)
open import Data.Word64.Base
open import Function.Base using (_$_; _|>_)

------------------------------------------------------------------------
-- Re-export primitives publicly

open import Data.Word64.Primitive as Prim public
  using ( show )

testBit : Word64 → Fin 64 → Bool
testBit w i = Prim.testBit w (Fin.toℕ i)

_[_]≔_ : Word64 → Fin 64 → Bool → Word64
w [ i ]≔ false = Prim.clearBit w (Fin.toℕ i)
w [ i ]≔ true  = Prim.setBit w (Fin.toℕ i)

------------------------------------------------------------------------
-- Convert to its components

toBits : Word64 → Vec Bool 64
toBits w = Vec.tabulate (testBit w)

fromBits : Vec Bool 64 → Word64
fromBits bs = Vec.foldl′ _|>_ (fromℕ 0)
            $ Vec.zipWith (λ i b → _[ i ]≔ b) (Vec.allFin 64) bs

toWord64s : Word64 → Vec Word8 8
toWord64s w =
  let ws = proj₁ (Vec.group 8 8 (toBits w)) in
  Vec.map Word8.fromBits ws
