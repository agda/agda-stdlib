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

li : 𝕋
li = T.leaf tt

ni : 𝕋 → 𝕋 → 𝕋
ni i₁ i₂ = T.node i₁ tt i₂

------------------------------------------------------------------------
-- ITree definition and basic functions

data ITree (N : Set n) (L : Set l) : 𝕋 → Set (n ⊔ l) where
  leaf : L → ITree N L li
  node : ∀ {i₁ i₂} → ITree N L i₁ → N → ITree N L i₂ → ITree N L (ni i₁ i₂)

map : ∀ {i} → (N → N₁) → (L → L₁) → ITree N L i → ITree N₁ L₁ i
map f g (leaf x) = leaf (g x)
map f g (node l m r) = node (map f g l) (f m) (map f g r)

mapₙ : ∀ {i} → (N → N₁) → ITree N L i → ITree N₁ L i
mapₙ f t = map f id t

mapₗ : ∀ {i} → (L → L₁) → ITree N L i → ITree N L₁ i
mapₗ g t = map id g t

#nodes : ∀ {i} → ITree N L i → ℕ
#nodes {i = i} t = T.#nodes i

#leaves : ∀ {i} → ITree N L i → ℕ
#leaves {i = i} t = T.#leaves i

foldr : ∀ {i} → (A → N → A → A) → (L → A) → ITree N L i → A
foldr f g (leaf x) = g x
foldr f g (node l m r) = f (foldr f g l) m (foldr f g r)

------------------------------------------------------------------------
-- Conversion to regular trees

toTree : ∀ {i} → ITree N L i → Tree N L
toTree (leaf x) = T.leaf x
toTree (node l m r) = T.node (toTree l) m (toTree r)

------------------------------------------------------------------------
-- Indexed lookups

data Index : 𝕋 → Set where
  here-l : Index li
  here-n : ∀ {i₁ i₂} → Index (ni i₁ i₂)
  go-l : ∀ {i₁ i₂} → Index i₁ → Index (ni i₁ i₂)
  go-r : ∀ {i₁ i₂} → Index i₂ → Index (ni i₁ i₂)

retrieve : ∀ {i} → ITree N L i → Index i → N ⊎ L
retrieve (leaf x) here-l = inj₂ x
retrieve (node l m r) here-n = inj₁ m
retrieve (node l m r) (go-l i) = retrieve l i
retrieve (node l m r) (go-r i) = retrieve r i

retrieve-subtree : ∀ {i} → ITree N L i → Index i → Tree N L
retrieve-subtree (leaf x) here-l = T.leaf x
retrieve-subtree (node l m r) here-n = toTree (node l m r)
retrieve-subtree (node l m r) (go-l i) = retrieve-subtree l i
retrieve-subtree (node l m r) (go-r i) = retrieve-subtree r i
