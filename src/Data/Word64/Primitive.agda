------------------------------------------------------------------------
-- The Agda standard library
--
-- Word64: simple bindings to Haskell types and functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Data.Word64.Primitive where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Word using (Word64)

postulate
  testBit : Word64 → Nat → Bool
  setBit : Word64 → Nat → Word64
  clearBit : Word64 → Nat → Word64
  show : Word64 → String

{-# FOREIGN GHC import GHC.Word #-}
{-# FOREIGN GHC import qualified Data.Bits as B #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}

{-# COMPILE GHC testBit = \ w -> B.testBit w . fromIntegral #-}
{-# COMPILE GHC setBit = \ w -> B.setBit w . fromIntegral #-}
{-# COMPILE GHC clearBit = \ w -> B.clearBit  w . fromIntegral #-}
{-# COMPILE GHC show = T.pack . Prelude.show #-}
