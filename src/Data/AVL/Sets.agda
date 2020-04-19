------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.AVL.Sets
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

{-# WARNING_ON_IMPORT
"Data.AVL.Sets was deprecated in v1.4.
Use Data.Tree.AVL.Sets instead."
#-}

open import Data.Tree.AVL.Sets strictTotalOrder public
