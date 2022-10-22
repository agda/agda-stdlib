------------------------------------------------------------------------
-- The Agda standard library
--
-- The Either type which calls out to Haskell via the FFI
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Foreign.Haskell.Either where

open import Level
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definition

data Either (A : Set a) (B : Set b) : Set (a ⊔ b) where
  left  : A → Either A B
  right : B → Either A B

{-# FOREIGN GHC type AgdaEither l1 l2 a b = Either a b #-}
{-# COMPILE GHC Either = data MAlonzo.Code.Foreign.Haskell.Either.AgdaEither (Left | Right) #-}

------------------------------------------------------------------------
-- Conversion

toForeign : A ⊎ B → Either A B
toForeign (inj₁ a) = left a
toForeign (inj₂ b) = right b
{-# WARNING_ON_USAGE toForeign
"Warning: toForeign was deprecated in 2.0.
Please use Foreign.Haskell.Coerce.coerce instead."
#-}

fromForeign : Either A B → A ⊎ B
fromForeign (left a)  = inj₁ a
fromForeign (right b) = inj₂ b
{-# WARNING_ON_USAGE fromForeign
"Warning: fromForeign was deprecated in 2.0.
Please use Foreign.Haskell.Coerce.coerce instead."
#-}
