------------------------------------------------------------------------
-- The Agda standard library
--
-- The Pair type implemented by calling out to Haskell via the FFI
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

record Pair (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field  fst : A
         snd : B
open Pair public

{-# FOREIGN GHC type AgdaPair l1 l2 a b = (a , b) #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Foreign.Haskell.AgdaPair ((,)) #-}

------------------------------------------------------------------------
-- Conversion

toForeign : A × B → Pair A B
toForeign (a , b) = (a , b)

fromForeign : Pair A B → A × B
fromForeign (a , b) = (a , b)
