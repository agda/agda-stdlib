------------------------------------------------------------------------
-- The Agda standard library
--
-- Bytestrings: simple types and functions
-- Note that these functions do not perform bound checks.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Data.Bytestring.Base where

open import Data.Nat.Base using (ℕ; _+_; _*_; _^_)
open import Agda.Builtin.String using (String)
import Data.Fin.Base as Fin
open import Data.Vec.Base as Vec using (Vec)
open import Data.Word8.Base as Word8 using (Word8)
open import Data.Word64.Base as Word64 using (Word64)

open import Function.Base using (const; _$_)

------------------------------------------------------------------------------
-- Re-export type and operations

open import Data.Bytestring.Primitive as Prim public
  using ( Bytestring
        ; length
        ; take
        ; drop
        ; show
        )
  renaming (index to getWord8)

------------------------------------------------------------------------------
-- Operations

slice : Word64 → Word64 → Bytestring → Bytestring
slice start chunk buf = take chunk (drop start buf)

------------------------------------------------------------------------------
-- Generic combinators for fixed-size encodings

getWord8s : (n : ℕ) → Bytestring → Word64 → Vec Word8 n
getWord8s n buf idx
  = let idx = Word64.toℕ idx in
  Vec.map (λ k → getWord8 buf (Word64.fromℕ (idx + Fin.toℕ k)))
  $ Vec.allFin n

-- Little endian representation:
-- Low place values first
fromWord8sLE : ∀ {n w} {W : Set w} → (fromℕ : ℕ → W) → Vec Word8 n → W
fromWord8sLE f ws = f (Vec.foldr′ (λ w acc → Word8.toℕ w + acc * (2 ^ 8)) 0 ws)

-- Big endian representation
-- Big place values first
fromWord8sBE : ∀ {n w} {W : Set w} → (fromℕ : ℕ → W) → Vec Word8 n → W
fromWord8sBE f ws = f (Vec.foldl′ (λ acc w → acc * (2 ^ 8) + Word8.toℕ w) 0 ws)

------------------------------------------------------------------------------
-- Decoding to a vector of bytes

toWord8s : (b : Bytestring) → Vec Word8 (length b)
toWord8s b = getWord8s _ b (Word64.fromℕ 0)

------------------------------------------------------------------------------
-- Getting Word64

getWord64LE : Bytestring → Word64 → Word64
getWord64LE buf idx
  = fromWord8sLE Word64.fromℕ (getWord8s 8 buf idx)

getWord64BE : Bytestring → Word64 → Word64
getWord64BE buf idx
  = fromWord8sBE Word64.fromℕ (getWord8s 8 buf idx)
