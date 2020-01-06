------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the pointwise lifting of a predicate to a binary tree
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary.Relation.Unary.All.Properties where

open import Level
open import Data.Tree.Binary as Tree using (Tree; leaf; node)
open import Data.Tree.Binary.Relation.Unary.All
open import Relation.Unary

private
  variable
    a b p q : Level
    A : Set a
    B : Set b

module _ {P : B → Set p} where

  map⁺ : (f : A → B) → ∀[ All (f ⊢ P) ⇒ Tree.map f ⊢ All P ]
  map⁺ f leaf         = leaf
  map⁺ f (node l m r) = node (map⁺ f l) m (map⁺ f r)
