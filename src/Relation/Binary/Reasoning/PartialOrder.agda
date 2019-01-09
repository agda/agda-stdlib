------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using a partial order
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Reasoning.PartialOrder
         {p₁ p₂ p₃} (P : Poset p₁ p₂ p₃) where

open Poset P
import Relation.Binary.Reasoning.Preorder as PreR
open PreR preorder public renaming (_∼⟨_⟩_ to _≤⟨_⟩_)
