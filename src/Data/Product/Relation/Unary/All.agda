------------------------------------------------------------------------
-- The Agda standard library
--
-- Lifting of two predicates
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Relation.Unary.All where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_×_; _,_)

private
  variable
    a b p q : Level
    A : Set a
    B : Set b

All : (A → Set p) → (B → Set q) → (A × B → Set (p ⊔ q))
All P Q (a , b) = P a × Q b
