------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- Data.List.Relation.Binary.Equality.Setoid directly.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Data.List.Relation.Equality.Setoid {a ℓ} (S : Setoid a ℓ) where

open import Data.List.Relation.Binary.Equality.Setoid S public
