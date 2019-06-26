------------------------------------------------------------------------
-- The Agda standard library
--
-- The Maybe type implemented by calling out to Haskell via the FFI
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Foreign.Haskell.Maybe where

open import Level
open import Data.Maybe as Data using (just; nothing)

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Definition

data Maybe (A : Set a) : Set a where
  just : A → Maybe A
  nothing : Maybe A

{-# FOREIGN GHC type AgdaMaybe l a = Maybe a #-}
{-# COMPILE GHC Maybe = data AgdaMaybe (Just | Nothing) #-}

------------------------------------------------------------------------
-- Conversion

toForeign : Data.Maybe A → Maybe A
toForeign (just x) = just x
toForeign nothing = nothing

fromForeign : Maybe A → Data.Maybe A
fromForeign (just x) = just x
fromForeign nothing = nothing
