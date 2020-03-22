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
    a b c d p q : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

module _ {P : C → Set p} {Q : D → Set q} where

  map⁺ : (f : A → C) → (g : B → D) → ∀[ All (f ⊢ P) (g ⊢ Q) ⇒ Tree.map f g ⊢ All P Q ]
  map⁺ f g (leaf x)     = leaf x
  map⁺ f g (node l m r) = node (map⁺ f g l) m (map⁺ f g r)
