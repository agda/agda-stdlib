------------------------------------------------------------------------
-- The Agda standard library
--
-- Type(s) used (only) when calling out to Haskell via the FFI
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Foreign.Haskell where

open import Level

-- A unit type.

open import Data.Unit using () renaming (⊤ to Unit; tt to unit) public

{-# WARNING_ON_USAGE Unit
"Warning: Unit was deprecated in v1.1.
Please use ⊤ from Data.Unit instead."
#-}

{-# WARNING_ON_USAGE unit
"Warning: unit was deprecated in v1.1.
Please use tt from Data.Unit instead."
#-}

-- A pair type

record Pair {ℓ ℓ′ : Level} (A : Set ℓ) (B : Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field  fst : A
         snd : B
open Pair public

{-# FOREIGN GHC type AgdaPair l1 l2 a b = (a , b) #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Foreign.Haskell.AgdaPair ((,)) #-}
