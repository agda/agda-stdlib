------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of a predicate to a binary tree
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary.Relation.Unary.All where

open import Level
open import Data.Tree.Binary as Tree using (Tree; leaf; node)
open import Relation.Unary

private
  variable
    a b p q : Level
    A : Set a
    B : Set b

data All {A : Set a} (P : A → Set p) : Tree A → Set (a ⊔ p) where
  leaf : All P leaf
  node : ∀ {l m r} → All P l → P m → All P r → All P (node l m r)

module _ {P : A → Set p} {Q : A → Set q} where

  map : ∀[ P ⇒ Q ] → ∀[ All P ⇒ All Q ]
  map f leaf         = leaf
  map f (node l m r) = node (map f l) (f m) (map f r)
