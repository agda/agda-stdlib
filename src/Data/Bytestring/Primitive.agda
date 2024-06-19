------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive bytestrings: simple bindings to Haskell types and functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Data.Bytestring.Primitive where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Word using (Word64)
open import Data.Word8.Primitive using (Word8)

-- NB: the bytestring package uses `Int` as the indexing type which
-- Haskell's base specifies as:
--
-- > A fixed-precision integer type with at least the range
-- > [-2^29 .. 2^29-1]. The exact range for a given implementation
-- > can be determined by using minBound and maxBound from the
-- > Bounded class.
--
-- There is no ergonomic way to encode that in a type-safe manner.
-- For now we use `Word64` with the understanding that using indices
-- greater than 2^29-1 may lead to undefined behaviours...

postulate
  Bytestring : Set
  index : Bytestring → Word64 → Word8
  length : Bytestring → Nat
  take : Word64 → Bytestring → Bytestring
  drop : Word64 → Bytestring → Bytestring
  show : Bytestring → String

{-# FOREIGN GHC import qualified Data.ByteString as B #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}

{-# COMPILE GHC Bytestring = type B.ByteString #-}
{-# COMPILE GHC index = \ buf idx -> B.index buf (fromIntegral idx) #-}
{-# COMPILE GHC length = \ buf -> fromIntegral (B.length buf) #-}
{-# COMPILE GHC take = B.take . fromIntegral #-}
{-# COMPILE GHC drop = B.drop . fromIntegral #-}
{-# COMPILE GHC show = T.pack . Prelude.show #-}
