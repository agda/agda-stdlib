------------------------------------------------------------------------
-- The Agda standard library
--
-- Integers
------------------------------------------------------------------------

-- See README.Data.Integer for examples of how to use and reason about
-- integers.

{-# OPTIONS --without-K --safe #-}

module Data.Integer where

------------------------------------------------------------------------
-- Re-export basic definition, operations and queries

open import Data.Integer.Base public
open import Data.Integer.Properties public
  using (_≡?_; _≤?_; _<?_)
