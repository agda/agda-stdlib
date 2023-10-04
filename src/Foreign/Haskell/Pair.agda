------------------------------------------------------------------------
-- The Agda standard library
--
-- The Pair type which calls out to Haskell via the FFI
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Foreign.Haskell.Pair where

open import Level
open import Data.Product.Base using (_×_; _,_)

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
infixr 4 _,_
open Pair public

{-# FOREIGN GHC type AgdaPair l1 l2 a b = (a , b) #-}
{-# COMPILE GHC Pair = data MAlonzo.Code.Foreign.Haskell.Pair.AgdaPair ((,)) #-}

------------------------------------------------------------------------
-- Conversion

toForeign : A × B → Pair A B
toForeign (a , b) = (a , b)
{-# WARNING_ON_USAGE toForeign
"Warning: toForeign was deprecated in 2.0.
Please use Foreign.Haskell.Coerce.coerce instead."
#-}

fromForeign : Pair A B → A × B
fromForeign (a , b) = (a , b)
{-# WARNING_ON_USAGE fromForeign
"Warning: fromForeign was deprecated in 2.0.
Please use Foreign.Haskell.Coerce.coerce instead."
#-}
