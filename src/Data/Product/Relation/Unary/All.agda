------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting of two predicates
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Relation.Unary.All where

open import Level
open import Data.Product
open import Function.Base
open import Relation.Unary

private
  variable
    a b p q : Level
    A : Set a
    B : Set b

All : (A → Set p) → (B → Set q) → (A × B → Set (p ⊔ q))
All P Q (a , b) = P a × Q b
