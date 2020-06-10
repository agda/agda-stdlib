------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use the builtin Maybe instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Foreign.Haskell.Maybe where

open import Level
open import Data.Maybe.Base as Data using (just; nothing)

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Definition

data Maybe (A : Set a) : Set a where
  just    : A → Maybe A
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


{-# WARNING_ON_IMPORT
"Warning: Foreign.Haskell.Maybe was deprecated in v1.4.
Maybe is now an Agda builtin and does not need library support."
#-}

{-# WARNING_ON_USAGE Maybe
"Warning: Foreign.Haskell.Maybe's Maybe was deprecated in v1.4.
Maybe is now an Agda builtin and does not need library support."
#-}

{-# WARNING_ON_USAGE toForeign
"Warning: toForeign was deprecated in v1.4.
Maybe is now an Agda builtin and does not need library support."
#-}

{-# WARNING_ON_USAGE fromForeign
"Warning: fromForeign was deprecated in v1.4.
Maybe is now an Agda builtin and does not need library support."
#-}
