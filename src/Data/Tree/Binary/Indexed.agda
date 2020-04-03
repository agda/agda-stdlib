------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed binary trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary.Indexed where

open import Data.Tree.Binary as T using (Tree)
open import Data.Unit
open import Level
open import Function.Base
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)

private
  variable
    a n n₁ l l₁ : Level
    N : Set n
    L : Set l
    N₁ : Set n₁
    L₁ : Set l₁
    A : Set a

------------------------------------------------------------------------
-- Type to represent the size of a tree

𝕋 : Set
𝕋 = Tree ⊤ ⊤

pattern ls = T.leaf tt

pattern ns s₁ s₂ = T.node s₁ tt s₂

------------------------------------------------------------------------
-- ITree definition and basic functions

data ITree (N : Set n) (L : Set l) : 𝕋 → Set (n ⊔ l) where
  leaf : L → ITree N L ls
  node : ∀ {s₁ s₂} → ITree N L s₁ → N → ITree N L s₂ → ITree N L (ns s₁ s₂)

map : ∀ {s} → (N → N₁) → (L → L₁) → ITree N L s → ITree N₁ L₁ s
map f g (leaf x) = leaf (g x)
map f g (node l m r) = node (map f g l) (f m) (map f g r)

mapₙ : ∀ {s} → (N → N₁) → ITree N L s → ITree N₁ L s
mapₙ f t = map f id t

mapₗ : ∀ {s} → (L → L₁) → ITree N L s → ITree N L₁ s
mapₗ g t = map id g t

#nodes : ∀ {s} → ITree N L s → ℕ
#nodes {s = s} t = T.#nodes s

#leaves : ∀ {s} → ITree N L s → ℕ
#leaves {s = s} t = T.#leaves s

foldr : ∀ {s} → (A → N → A → A) → (L → A) → ITree N L s → A
foldr f g (leaf x) = g x
foldr f g (node l m r) = f (foldr f g l) m (foldr f g r)

------------------------------------------------------------------------
-- Conversion to regular trees

toTree : ∀ {s} → ITree N L s → Tree N L
toTree (leaf x) = T.leaf x
toTree (node l m r) = T.node (toTree l) m (toTree r)

------------------------------------------------------------------------
-- Indexed lookups

data Index : 𝕋 → Set where
  here-l : Index ls
  here-n : ∀ {i₁ i₂} → Index (ns i₁ i₂)
  go-l : ∀ {i₁ i₂} → Index i₁ → Index (ns i₁ i₂)
  go-r : ∀ {i₁ i₂} → Index i₂ → Index (ns i₁ i₂)

infixl 3 _-_

_-_ : (s : 𝕋) → Index s → 𝕋
ls     - here-l = ls
ns l r - here-n = ns l r
ns l r - go-l i = l - i
ns l r - go-r i = r - i

retrieve : ∀ {s} → ITree N L s → Index s → N ⊎ L
retrieve (leaf x) here-l = inj₂ x
retrieve (node l m r) here-n = inj₁ m
retrieve (node l m r) (go-l i) = retrieve l i
retrieve (node l m r) (go-r i) = retrieve r i

retrieve-subtree : ∀ {s} → ITree N L s → (i : Index s) → ITree N L (s - i)
retrieve-subtree (leaf x) here-l       = leaf x
retrieve-subtree (node l m r) here-n   = node l m r
retrieve-subtree (node l m r) (go-l i) = retrieve-subtree l i
retrieve-subtree (node l m r) (go-r i) = retrieve-subtree r i

map-index : ∀ {s} → (i : Index s) → (ITree N L (s - i) → ITree N L (s - i)) → ITree N L s → ITree N L s
map-index here-l f t = f t
map-index here-n f t = f t
map-index (go-l i) f (node l m r) = node (map-index i f l) m r
map-index (go-r i) f (node l m r) = node l m (map-index i f r)
