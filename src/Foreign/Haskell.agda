------------------------------------------------------------------------
-- The Agda standard library
--
-- Type(s) used (only) when calling out to Haskell via the FFI
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Foreign.Haskell where

open import Level

-- A pair type

record Pair {ℓ ℓ′ : Level} (A : Set ℓ) (B : Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field  fst : A
         snd : B
open Pair public

{-# FOREIGN GHC type AgdaPair l1 l2 a b = (a , b) #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Foreign.Haskell.AgdaPair ((,)) #-}

-- Maybe

data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
  just : A → Maybe A
  nothing : Maybe A

{-# FOREIGN GHC type AgdaMaybe l a = Maybe a #-}
{-# COMPILE GHC Maybe = data AgdaMaybe (Just | Nothing) #-}


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

open import Data.Unit using (⊤; tt)

-- Version 1.1

Unit = ⊤
{-# WARNING_ON_USAGE Unit
"Warning: Unit was deprecated in v1.1.
Please use ⊤ from Data.Unit instead."
#-}
unit = tt
{-# WARNING_ON_USAGE unit
"Warning: unit was deprecated in v1.1.
Please use tt from Data.Unit instead."
#-}
