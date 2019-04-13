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
{-# WARNING_ON_USAGE Unit "DEPRECATED: Use `⊤` instead of `Unit`" #-}
{-# WARNING_ON_USAGE unit "DEPRECATED: Use `tt` instead of `unit`" #-}

-- A pair type

record Pair {ℓ ℓ′ : Level} (A : Set ℓ) (B : Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field  fst : A
         snd : B
open Pair public

{-# FOREIGN GHC type AgdaPair l1 l2 a b = (a , b) #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Foreign.Haskell.AgdaPair ((,)) #-}
