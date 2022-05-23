------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Semigroup
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Ordered using (Prokleenealgebra)

module Algebra.Ordered.Properties.KleeneAlgebra {a ℓ₁ ℓ₂} (K : Prokleenealgebra a ℓ₁ ℓ₂) where

open Prokleenealgebra K