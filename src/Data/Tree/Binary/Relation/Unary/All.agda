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
open import Relation.Unary.Properties using (⊆-refl)

private
  variable
    n l p q r s : Level
    N : Set n
    L : Set l
    P : N → Set p
    Q : L → Set q
    R : N → Set r
    S : L → Set s

data All {N : Set n} {L : Set l} (P : N → Set p) (Q : L → Set q) : Tree N L → Set (n ⊔ l ⊔ p ⊔ q) where
  leaf : ∀ {x} → Q x → All P Q (leaf x)
  node : ∀ {l m r} → All P Q l → P m → All P Q r → All P Q (node l m r)

map : ∀[ P ⇒ R ] → ∀[ Q ⇒ S ] → ∀[ All P Q ⇒ All R S ]
map f g (leaf x)     = leaf (g x)
map f g (node l m r) = node (map f g l) (f m) (map f g r)

mapₙ : ∀[ P ⇒ R ] → ∀[ All P Q ⇒ All R Q ]
mapₙ {Q = Q} f = map f (⊆-refl {x = Q})

mapₗ : ∀[ Q ⇒ S ] → ∀[ All P Q ⇒ All P S ]
mapₗ {P = P} f = map (⊆-refl {x = P}) f
