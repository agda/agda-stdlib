------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
-----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Data.AVL.Key
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

{-# WARNING_ON_IMPORT
"Data.AVL.Key was deprecated in v1.4.
Use Data.Tree.AVL.Key instead."
#-}

open import Data.Tree.AVL.Key strictTotalOrder public
