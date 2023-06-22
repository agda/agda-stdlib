------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of enumerability 
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Unary.Enumerable where

  open import Data.Fin using (Fin)
  open import Data.Nat using (ℕ)
  open import Level using (Level)
  open import Function.Bundles using (_↔_)

  record IsEnumerable {x : Level} (X : Set x) : Set x where 
      field
        size : ℕ
        enum : Fin size ↔ X

