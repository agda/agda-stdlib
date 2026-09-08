------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational where

------------------------------------------------------------------------
-- Publicly re-export contents of core module and queries

open import Data.Rational.Base public
open import Data.Rational.Properties public
  using (_≟_; _≤?_; _<?_; _≥?_; _>?_)
