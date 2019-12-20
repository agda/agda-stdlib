------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers
------------------------------------------------------------------------

-- See README.Data.Nat for examples of how to use and reason about
-- naturals.

{-# OPTIONS --without-K --safe #-}

module Data.Nat where

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Data.Nat.Base public

------------------------------------------------------------------------
-- Publicly re-export queries

open import Data.Nat.Properties public
  using
  ( _≟_
  ; _≤?_ ; _≥?_ ; _<?_ ; _>?_
  ; _≤′?_; _≥′?_; _<′?_; _>′?_
  ; _≤″?_; _<″?_; _≥″?_; _>″?_
  )

------------------------------------------------------------------------
-- Deprecated

-- Version 0.17

open import Data.Nat.Properties public
  using (≤-pred)
