------------------------------------------------------------------------
-- The Agda standard library
--
-- The NonEmpty type which calls out to Haskell via the FFI
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Foreign.Haskell.List.NonEmpty where

open import Level
open import Data.List.NonEmpty.Base as Data using (_∷_)
open import Data.List using (List)

{-# FOREIGN GHC import qualified Data.List.NonEmpty as NE #-}

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Definition

data NonEmpty (A : Set a) : Set a where
  _∷_ : A → List A → NonEmpty A

{-# FOREIGN GHC type AgdaNonEmpty l a = NE.NonEmpty a #-}
{-# COMPILE GHC NonEmpty = data AgdaNonEmpty ((NE.:|)) #-}
