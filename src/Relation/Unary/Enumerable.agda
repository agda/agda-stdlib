------------------------------------------------------------------------
-- The Agda standard library
--
-- Enumerable definition 
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Unary.Enumerable where

  open import Data.Fin using (Fin)
  open import Data.Nat using (ℕ)
  open import Level using (Level)
  open import Function.Bundles using (_↔_)

  record IsEnumerable {a : Level} (A : Set a) : Set a where 
      field
        size : ℕ
        enum : Fin size ↔ A

