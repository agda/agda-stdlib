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
open import Function

private
  variable
    n l n₁ l₁ p q : Level
    N : Set n
    L : Set l
    N₁ : Set n₁
    L₁ : Set l₁
    P : N₁ → Set p
    Q : L₁ → Set q

map⁺ : (f : N → N₁) → (g : L → L₁) → All (f ⊢ P) (g ⊢ Q) ⊆ Tree.map f g ⊢ All P Q
map⁺ f g (leaf x)     = leaf x
map⁺ f g (node l m r) = node (map⁺ f g l) m (map⁺ f g r)

mapₙ⁺ : (f : N → N₁) → All (f ⊢ P) Q ⊆ Tree.mapₙ f ⊢ All P Q
mapₙ⁺ f = map⁺ f id

mapₗ⁺ : (g : L → L₁) → All P (g ⊢ Q) ⊆ Tree.mapₗ g ⊢ All P Q
mapₗ⁺ g = map⁺ id g
