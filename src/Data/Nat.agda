------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers
------------------------------------------------------------------------

-- See README.Data.Nat for examples of how to use and reason about
-- naturals.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat where

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Data.Nat.Base public

------------------------------------------------------------------------
-- Publicly re-export queries

open import Data.Nat.Properties public
  using
  -- key values
  ( nonZero?
  -- equalities
  ; _≟_ ; eq?
  -- standard orders & their relationship
  ; _≤?_ ; _≥?_ ; _<?_ ; _>?_
  ; ≤-<-connex ; ≥->-connex ; <-≤-connex ; >-≥-connex
  ; <-cmp
  -- alternative definitions of the orders
  ; _≤′?_; _≥′?_; _<′?_; _>′?_
  ; _≤″?_; _<″?_; _≥″?_; _>″?_
  ; _<‴?_; _≤‴?_; _≥‴?_; _>‴?_
  -- bounded predicates
  ; anyUpTo? ; allUpTo?
  )

------------------------------------------------------------------------
-- Deprecated

-- Version 0.17

open import Data.Nat.Properties public
  using (≤-pred)
