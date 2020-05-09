------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Product as Prod
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst)
import Data.Tree.AVL.Value

module Data.AVL.IndexedMap
  {i k v ℓ}
  {Index : Set i} {Key : Index → Set k}  (Value : Index → Set v)
  {_<_ : Rel (∃ Key) ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

{-# WARNING_ON_IMPORT
"Data.AVL.IndexedMap was deprecated in v1.4.
Use Data.Tree.AVL.IndexedMap instead."
#-}

open import Data.Tree.AVL.IndexedMap Value isStrictTotalOrder public
