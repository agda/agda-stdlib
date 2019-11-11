------------------------------------------------------------------------
-- The Agda standard library
--
-- This file contains some core definitions which are re-exported by
-- Data.List.Relation.Binary.Sublist.Heterogeneous.
------------------------------------------------------------------------

-- This module has R as explicit parameter, in contrast to the implicit
-- parameter R of the main module Sublist.Heterogeneous.

-- Parameterized data modules (https://github.com/agda/agda/issues/3210)
-- may simplify this setup, making this module obsolete.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (REL)

module Data.List.Relation.Binary.Sublist.Heterogeneous.Core
       {a b r} {A : Set a} {B : Set b} (R : REL A B r)
       where

open import Level using (_⊔_)
open import Data.List.Base using (List; []; _∷_)

infixr 5 _∷_ _∷ʳ_

data Sublist : REL (List A) (List B) (a ⊔ b ⊔ r) where
  []   : Sublist [] []
  _∷ʳ_ : ∀ {xs ys} → ∀ y → Sublist xs ys → Sublist xs (y ∷ ys)
  _∷_  : ∀ {x xs y ys} → R x y → Sublist xs ys → Sublist (x ∷ xs) (y ∷ ys)
