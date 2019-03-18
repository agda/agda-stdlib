------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the sublist relation with respect to a setoid
-- which is decidable. This is a generalisation of what is commonly known as
-- Order Preserving Embeddings (OPE).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (DecSetoid)

module Data.List.Relation.Binary.Sublist.DecSetoid {c ℓ} (S : DecSetoid c ℓ) where

private
  module S = DecSetoid S

open import Data.List.Relation.Binary.Sublist.Setoid S.setoid public
