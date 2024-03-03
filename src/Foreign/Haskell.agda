------------------------------------------------------------------------
-- The Agda standard library
--
-- Type(s) used (only) when calling out to Haskell via the FFI
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Foreign.Haskell where

open import Level

------------------------------------------------------------------------
-- Pairs

open import Foreign.Haskell.Pair public
  renaming
  ( toForeign   to toForeignPair
  ; fromForeign to fromForeignPair
  )

------------------------------------------------------------------------
-- Sums

open import Foreign.Haskell.Either public
  renaming
  ( toForeign   to toForeignEither
  ; fromForeign to fromForeignEither
  )
