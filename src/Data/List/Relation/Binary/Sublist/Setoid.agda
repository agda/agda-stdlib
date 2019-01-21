------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the sublist relation with respect to a setoid
-- This is a generalisation of what is commonly known as Order Preserving
-- Embeddings (OPE).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; Rel)

module Data.List.Relation.Sublist.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Level using (_⊔_)
open import Data.List.Base using (List; []; _∷_)
import Data.List.Relation.Sublist.Heterogeneous as Sublist

private
  module S = Setoid S
  open S renaming (Carrier to A)

_⊆_ : Rel (List A) (c ⊔ ℓ)
_⊆_ = Sublist.Sublist _≈_

open Sublist hiding (Sublist) public
