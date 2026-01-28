------------------------------------------------------------------------
-- The Agda standard library
--
-- Booleans
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Bool where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

------------------------------------------------------------------------
-- The boolean type and some operations

open import Data.Bool.Base public

------------------------------------------------------------------------
-- Publicly re-export queries

open import Data.Bool.Properties public
  using (T?; _≟_; _≤?_; _<?_)

------------------------------------------------------------------------
-- Other functions

contradiction : ∀ {w} {Whatever : Set w} {b} → b ≡ true → b ≡ false → Whatever
contradiction refl ()
