------------------------------------------------------------------------
-- The Agda standard library
--
-- Which Maybe type which calls out to Haskell via the FFI
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Foreign.Haskell.Maybe where

open import Level
import Data.Maybe as Data

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Definition

abstract

  Maybe : Set a → Set a
  Maybe = Data.Maybe

{-# FOREIGN GHC type AgdaMaybe l a = Maybe a #-}
{-# COMPILE GHC Maybe = data AgdaMaybe (Just | Nothing) #-}

------------------------------------------------------------------------
-- Conversion

abstract

  toForeign : Data.Maybe A → Maybe A
  toForeign x = x

  fromForeign : Maybe A → Data.Maybe A
  fromForeign x = x
