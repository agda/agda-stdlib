------------------------------------------------------------------------
-- The Agda standard library
--
-- Universes
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Universe where

open import Data.Product
open import Level

------------------------------------------------------------------------
-- Definition

record Universe u e : Set (suc (u ⊔ e)) where
  field
    U : Set u       -- Codes.
    El : U → Set e  -- Decoding function.
