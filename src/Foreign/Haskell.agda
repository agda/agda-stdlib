------------------------------------------------------------------------
-- The Agda standard library
--
-- Type(s) used (only) when calling out to Haskell via the FFI
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Foreign.Haskell where

open import Level

-- A unit type.

data Unit : Set where
  unit : Unit

{-# COMPILE GHC Unit = data () (()) #-}
{-# COMPILE UHC Unit = data __UNIT__ (__UNIT__) #-}

-- A pair type

record Pair {ℓ ℓ′ : Level} (A : Set ℓ) (B : Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field  fst : A
         snd : B
open Pair public

{-# FOREIGN GHC type AgdaPair l1 l2 a b = (a , b) #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Foreign.Haskell.AgdaPair ((,)) #-}
