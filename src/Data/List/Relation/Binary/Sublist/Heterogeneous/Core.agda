------------------------------------------------------------------------
-- The Agda standard library
--
-- This file contains some core definitions which are re-exported by
-- Data.List.Relation.Binary.Sublist.Heterogeneous.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (REL)

module Data.List.Relation.Binary.Sublist.Heterogeneous.Core
       {a b r} {A : Set a} {B : Set b} (R : REL A B r)
       where

open import Level using (_⊔_)
open import Data.List.Base using (List; []; _∷_; [_])

data Sublist : REL (List A) (List B) (a ⊔ b ⊔ r) where
  []   : Sublist [] []
  _∷ʳ_ : ∀ {xs ys} → ∀ y → Sublist xs ys → Sublist xs (y ∷ ys)
  _∷_  : ∀ {x xs y ys} → R x y → Sublist xs ys → Sublist (x ∷ xs) (y ∷ ys)
