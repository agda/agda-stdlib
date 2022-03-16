------------------------------------------------------------------------
-- The Agda standard library
--
-- Booleans
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bool where

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

------------------------------------------------------------------------
-- The boolean type and some operations

open import Data.Bool.Base public

------------------------------------------------------------------------
-- Publicly re-export queries

open import Data.Bool.Properties public
  using (T?; _≟_; _≤?_; _<?_)
