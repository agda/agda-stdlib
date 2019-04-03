------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the sublist relation with respect to a setoid
-- This is a generalisation of what is commonly known as Order Preserving
-- Embeddings (OPE).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; Rel)

module Data.List.Relation.Binary.Sublist.Setoid {c ℓ} (S : Setoid c ℓ) where

open import Level using (_⊔_)
open import Data.List.Base using (List; []; _∷_)

private
  module S = Setoid S
  open S renaming (Carrier to A)

open import Data.List.Relation.Binary.Sublist.Heterogeneous {R = _≈_}
  as Sublist
  hiding (Sublist; []; _∷_; _∷ʳ_)
  public

open import Data.List.Relation.Binary.Sublist.Heterogeneous.Core _≈_ public

infix 4 _⊆_
_⊆_ : Rel (List A) (c ⊔ ℓ)
_⊆_ = Sublist.Sublist _≈_
