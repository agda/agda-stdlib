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
    a b c d p q r s : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

data All {A : Set a} {B : Set b} (P : A → Set p) (Q : B → Set q) : Tree A B → Set (a ⊔ b ⊔ p ⊔ q) where
  leaf : ∀ {x} → Q x → All P Q (leaf x)
  node : ∀ {l m r} → All P Q l → P m → All P Q r → All P Q (node l m r)

module _ {P : A → Set p} {Q : B → Set q} {R : A → Set r} {S : B → Set s} where

  map : ∀[ P ⇒ R ] → ∀[ Q ⇒ S ] → ∀[ All P Q ⇒ All R S ]
  map f g (leaf x)     = leaf (g x)
  map f g (node l m r) = node (map f g l) (f m) (map f g r)
