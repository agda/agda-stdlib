------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of leaf labelled binary trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary.LeafLabelled.Properties where

open import Level using (Level)
open import Data.Nat.Base using (suc; _+_)
open import Data.Tree.Binary.LeafLabelled
open import Function.Base
open import Relation.Binary.PropositionalEquality

private
  variable
    a b : Level
    A : Set a
    B : Set b

size-map : ∀ (f : A → B) t → size (map f t) ≡ size t
size-map f (leaf x) = refl
size-map f (node l r) = cong₂ _+_ (size-map f l) (size-map f r)

map-id : ∀ (t : LTree A) → map id t ≡ t
map-id (leaf x) = refl
map-id (node l r) = cong₂ node (map-id l) (map-id r)
