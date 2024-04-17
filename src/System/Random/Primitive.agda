------------------------------------------------------------------------
-- The Agda standard library
--
-- Primitive System.Random simple bindings to Haskell functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module System.Random.Primitive where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Word using (Word64)
open import Foreign.Haskell.Pair using (Pair)

postulate
  randomIO-Char : IO Char
  randomRIO-Char : Pair Char Char → IO Char
  randomIO-Int : IO Int
  randomRIO-Int : Pair Int Int → IO Int
  randomIO-Float : IO Float
  randomRIO-Float : Pair Float Float → IO Float
  randomIO-Nat : IO Nat
  randomRIO-Nat : Pair Nat Nat → IO Nat
  randomIO-Word64 : IO Word64
  randomRIO-Word64 : Pair Word64 Word64 → IO Word64

{-# FOREIGN GHC import System.Random #-}

{-# COMPILE GHC randomIO-Char = randomIO #-}
{-# COMPILE GHC randomRIO-Char = randomRIO #-}
{-# COMPILE GHC randomIO-Int = randomIO #-}
{-# COMPILE GHC randomRIO-Int = randomRIO #-}
{-# COMPILE GHC randomIO-Float = randomIO #-}
{-# COMPILE GHC randomRIO-Float = randomRIO #-}
{-# COMPILE GHC randomIO-Nat = abs <$> randomIO #-}
{-# COMPILE GHC randomRIO-Nat = randomRIO #-}
{-# COMPILE GHC randomIO-Word64 = randomIO #-}
{-# COMPILE GHC randomRIO-Word64 = randomRIO #-}
