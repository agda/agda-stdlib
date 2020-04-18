------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
-----------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Data.AVL.Value {a ℓ} (S : Setoid a ℓ) where

{-# WARNING_ON_IMPORT
"Data.AVL.Value was deprecated in v1.4.
Use Data.Tree.AVL.Value instead."
#-}

open import Data.Tree.AVL.Value S public
