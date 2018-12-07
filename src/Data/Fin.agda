------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite sets
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Fin where

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Data.Fin.Base public

------------------------------------------------------------------------
-- Publicly re-export queries

open import Data.Fin.Properties public
  using (_≟_; _≤?_; _<?_)
