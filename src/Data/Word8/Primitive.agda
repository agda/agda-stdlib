------------------------------------------------------------------------
-- The Agda standard library
--
-- Bytes: simple bindings to Haskell types and functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Data.Word8.Primitive where

open import Agda.Builtin.Nat using (Nat)

postulate
  Word8 : Set
  fromNat : Nat → Word8
  toNat : Word8 → Nat
  _+_ : Word8 → Word8 → Word8

{-# FOREIGN GHC import GHC.Word #-}

{-# COMPILE GHC Word8 = type Word8 #-}
{-# COMPILE GHC fromNat = fromIntegral #-}
{-# COMPILE GHC toNat = fromIntegral #-}
{-# COMPILE GHC _+_ = (+) #-}
