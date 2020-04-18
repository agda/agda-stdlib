------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

module Data.AVL.Indexed.WithK
       {k r} (Key : Set k) {_<_ : Rel Key r}
       (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) where

{-# WARNING_ON_IMPORT
"Data.AVL.Indexed.WithK was deprecated in v1.4.
Use Data.Tree.AVL.Indexed.WithK instead."
#-}

open import Data.Tree.AVL.Indexed.WithK Key isStrictTotalOrder public
