------------------------------------------------------------------------
-- The Agda standard library
--
-- Bytestrings: builder type and functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Data.Bytestring.Builder.Base where

open import Data.Nat.Base using (ℕ; zero; suc; _/_; _%_; _^_)
open import Data.Word8.Base as Word8 using (Word8)
open import Data.Word64.Base as Word64 using (Word64)
open import Function.Base using (_∘′_)

------------------------------------------------------------------------------
-- Re-export type and operations

open import Data.Bytestring.Builder.Primitive as Prim public
  using ( Builder
        ; toBytestring
        ; bytestring
        ; word8
        ; empty
        ; _<>_
        )

------------------------------------------------------------------------------
-- High-level combinators

module List where

  open import Data.List.Base as List using (List)

  concat : List Builder → Builder
  concat = List.foldr _<>_ empty

module Vec where

  open import Data.Vec.Base as Vec using (Vec)

  concat : ∀ {n} → Vec Builder n → Builder
  concat = Vec.foldr′ _<>_ empty
open Vec

------------------------------------------------------------------------------
-- Generic word-specific combinators

open import Data.Vec.Base as Vec using (Vec; []; _∷_)

wordN : ∀ {n} → Vec Word8 n → Builder
wordN = concat ∘′ Vec.map word8

toWord8sLE : ∀ {w} {W : Set w} (n : ℕ) (toℕ : W → ℕ) → W → Vec Word8 n
toWord8sLE n toℕ w = loop (toℕ w) n where

  loop : ℕ → (n : ℕ) → Vec Word8 n
  loop acc 0 = []
  loop acc 1 = Word8.fromℕ acc ∷ []
  loop acc (suc n) = Word8.fromℕ (acc % 2 ^ 8) ∷ loop (acc / 2 ^ 8) n

toWord8sBE : ∀ {w} {W : Set w} (n : ℕ) (toℕ : W → ℕ) → W → Vec Word8 n
toWord8sBE n toℕ w = Vec.reverse (toWord8sLE n toℕ w)

------------------------------------------------------------------------------
-- Builders for Word64

word64LE : Word64 → Builder
word64LE w = wordN (toWord8sLE 8 Word64.toℕ w)

word64BE : Word64 → Builder
word64BE w = wordN (toWord8sBE 8 Word64.toℕ w)
