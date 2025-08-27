------------------------------------------------------------------------
-- The Agda standard library
--
-- Bytes: simple bindings to Haskell types and functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Data.Word8.Primitive where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

postulate
  Word8 : Set
  testBit : Word8 → Nat → Bool
  setBit : Word8 → Nat → Word8
  clearBit : Word8 → Nat → Word8
  fromNat : Nat → Word8
  toNat : Word8 → Nat
  _+_ : Word8 → Word8 → Word8
  show : Word8 → String

{-# FOREIGN GHC import GHC.Word #-}
{-# FOREIGN GHC import qualified Data.Bits as B #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}

{-# COMPILE GHC Word8 = type Word8 #-}
{-# COMPILE GHC testBit = \ w -> B.testBit w . fromIntegral #-}
{-# COMPILE GHC setBit = \ w -> B.setBit w . fromIntegral #-}
{-# COMPILE GHC clearBit = \ w -> B.clearBit  w . fromIntegral #-}
{-# COMPILE GHC fromNat = fromIntegral #-}
{-# COMPILE GHC toNat = fromIntegral #-}
{-# COMPILE GHC _+_ = (+) #-}
{-# COMPILE GHC show = T.pack . Prelude.show #-}
