------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers in non-reduced form.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Rational.Unnormalised where

-- Re-export basic definition, operations and queries

open import Data.Rational.Unnormalised.Base public
open import Data.Rational.Unnormalised.Properties public
  using (_≃?_; _≤?_; _<?_; _≥?_; _>?_)
