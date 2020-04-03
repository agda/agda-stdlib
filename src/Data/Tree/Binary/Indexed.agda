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

data IndexLeaf : 𝕋 → Set where
  here-l : IndexLeaf ls
  il-l : ∀ {s₁ s₂} → IndexLeaf s₁ → IndexLeaf (ns s₁ s₂)
  il-r : ∀ {s₁ s₂} → IndexLeaf s₂ → IndexLeaf (ns s₁ s₂)

data IndexTree : 𝕋 → Set where
  here-t : ∀ {s} → IndexTree s
  it-l : ∀ {s₁ s₂} → IndexTree s₁ → IndexTree (ns s₁ s₂)
  it-r : ∀ {s₁ s₂} → IndexTree s₂ → IndexTree (ns s₁ s₂)

infixl 3 _-_

_-_ : (s : 𝕋) → IndexTree s → 𝕋
t      - here-t = t
ns l r - it-l i = l - i
ns l r - it-r i = r - i

retrieve-leaf : ∀ {s} → ITree N L s → IndexLeaf s → L
retrieve-leaf (leaf x)     here-l   = x
retrieve-leaf (node l m r) (il-l i) = retrieve-leaf l i
retrieve-leaf (node l m r) (il-r i) = retrieve-leaf r i

retrieve-subtree : ∀ {s} → ITree N L s → (i : IndexTree s) → ITree N L (s - i)
retrieve-subtree t             here-t  = t
retrieve-subtree (node l m r) (it-l i) = retrieve-subtree l i
retrieve-subtree (node l m r) (it-r i) = retrieve-subtree r i

update-index : ∀ {s} → (L → L) → ITree N L s → IndexLeaf s → ITree N L s
update-index f (leaf x)      here-l  = leaf (f x)
update-index f (node l m r) (il-l i) = node (update-index f l i) m r
update-index f (node l m r) (il-r i) = node l m (update-index f r i)
