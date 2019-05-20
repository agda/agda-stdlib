------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed universes
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Universe.Indexed where

open import Data.Product
open import Data.Universe
open import Function
open import Level

------------------------------------------------------------------------
-- Definitions

record IndexedUniverse i u e : Set (suc (i ⊔ u ⊔ e)) where
  field
    I  : Set i                 -- Index set.
    U  : I → Set u             -- Codes.
    El : ∀ {i} → U i → Set e   -- Decoding function.

  -- An indexed universe can be turned into an unindexed one.

  unindexed-universe : Universe (i ⊔ u) e
  unindexed-universe = record
    { U  = ∃ λ i → U i
    ; El = El ∘ proj₂
    }
