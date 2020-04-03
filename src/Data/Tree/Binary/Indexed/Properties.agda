------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of indexed binary trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary.Indexed.Properties where

open import Level
open import Data.Tree.Binary.Indexed
open import Data.Tree.Binary.Properties as P using ()
open import Relation.Binary.PropositionalEquality
open import Function.Base

private
  variable
    a n n₁ l l₁ : Level
    A : Set a
    N : Set n
    N₁ : Set n₁
    L : Set l
    L₁ : Set l₁
    s : 𝕋


#nodes-map : ∀ (f : N → N₁) (g : L → L₁) (t : ITree N L s) → #nodes (map f g t) ≡ #nodes t
#nodes-map f g t = refl

#nodes-mapₙ : ∀ (f : N → N₁) (t : ITree N L s) → #nodes (mapₙ f t) ≡ #nodes t
#nodes-mapₙ f t = refl

#nodes-mapₗ : ∀ (g : L → L₁) (t : ITree N L s) → #nodes (mapₗ g t) ≡ #nodes t
#nodes-mapₗ g t = refl

#leaves-map : ∀ (f : N → N₁) (g : L → L₁) (t : ITree N L s) → #leaves (map f g t) ≡ #leaves t
#leaves-map f g t = refl

#leaves-mapₙ : ∀ (f : N → N₁) (t : ITree N L s) → #leaves (mapₙ f t) ≡ #leaves t
#leaves-mapₙ f t = refl

#leaves-mapₗ : ∀ (g : L → L₁) (t : ITree N L s) → #leaves (mapₗ g t) ≡ #leaves t
#leaves-mapₗ g t = refl

map-id : ∀ (t : ITree N L s) → map id id t ≡ t
map-id (leaf x) = refl
map-id (node l m r) = cong₂ (flip node m) (map-id l) (map-id r)

------------------------------------------------------------------------
-- Relation between retrievals and maps

retrieve-leaf-map : (f : N → N₁) →
                    (g : L → L₁) →
                    (t : ITree N L s) →
                    (i : IndexLeaf s) →
                    retrieve-leaf (map f g t) i ≡ g (retrieve-leaf t i)
retrieve-leaf-map f g (leaf x)      here-l  = refl
retrieve-leaf-map f g (node l m r) (il-l i) = retrieve-leaf-map f g l i
retrieve-leaf-map f g (node l m r) (il-r i) = retrieve-leaf-map f g r i

retrieve-subtree-map : (f : N → N₁) →
                       (g : L → L₁) →
                       (t : ITree N L s) →
                       (i : IndexTree s) →
                       retrieve-subtree (map f g t) i ≡ map f g (retrieve-subtree t i)
retrieve-subtree-map f g t             here-t  = refl
retrieve-subtree-map f g (node l m r) (it-l i) = retrieve-subtree-map f g l i
retrieve-subtree-map f g (node l m r) (it-r i) = retrieve-subtree-map f g r i

retrieve-leaf-update : (f : N → N₁) →
                       (g : L → L) →
                       (t : ITree N L s) →
                       (i : IndexLeaf s) →
                       retrieve-leaf (update-index g t i) i ≡ g (retrieve-leaf t i)
retrieve-leaf-update f g (leaf x)      here-l  = refl
retrieve-leaf-update f g (node l m r) (il-l i) = retrieve-leaf-update f g l i
retrieve-leaf-update f g (node l m r) (il-r i) = retrieve-leaf-update f g r i
