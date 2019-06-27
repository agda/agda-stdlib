------------------------------------------------------------------------
-- The Agda standard library
--
-- The Pair type which calls out to Haskell via the FFI
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Foreign.Haskell.Pair where

open import Level
open import Data.Product using (_×_; _,_)

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definition

abstract

  Pair : Set a → Set b → Set (a ⊔ b)
  Pair = _×_

{-# FOREIGN GHC type AgdaPair l1 l2 a b = (a , b) #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Foreign.Haskell.AgdaPair ((,)) #-}

------------------------------------------------------------------------
-- Conversion

abstract

  toForeign : A × B → Pair A B
  toForeign x = x

  fromForeign : Pair A B → A × B
  fromForeign x = x
