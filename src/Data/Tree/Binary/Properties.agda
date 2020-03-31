------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of binary trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary.Properties where

open import Level using (Level)
open import Data.Nat.Base using (suc; _+_)
open import Data.Tree.Binary
open import Function.Base
open import Relation.Binary.PropositionalEquality

private
  variable
    a n n₁ l l₁ : Level
    A : Set a
    N : Set n
    N₁ : Set n₁
    L : Set l
    L₁ : Set l₁

#nodes-map : ∀ (f : N → N₁) (g : L → L₁) t → #nodes (map f g t) ≡ #nodes t
#nodes-map f g (leaf x)     = refl
#nodes-map f g (node l m r) =
  cong₂ (λ l r → l + suc r) (#nodes-map f g l) (#nodes-map f g r)

#nodes-map₁ : ∀ (f : N → N₁) (t : Tree N L) → #nodes (map₁ f t) ≡ #nodes t
#nodes-map₁ f = #nodes-map f id

#nodes-map₂ : ∀ (g : L → L₁) (t : Tree N L) → #nodes (map₂ g t) ≡ #nodes t
#nodes-map₂ = #nodes-map id

#leaves-map : ∀ (f : N → N₁) (g : L → L₁) t → #leaves (map f g t) ≡ #leaves t
#leaves-map f g (leaf x)     = refl
#leaves-map f g (node l m r) =
  cong₂ _+_ (#leaves-map f g l) (#leaves-map f g r)

#leaves-map₁ : ∀ (f : N → N₁) (t : Tree N L) → #leaves (map₁ f t) ≡ #leaves t
#leaves-map₁ f = #leaves-map f id

#leaves-map₂ : ∀ (g : L → L₁) (t : Tree N L) → #leaves (map₂ g t) ≡ #leaves t
#leaves-map₂ = #leaves-map id

map-id : ∀ (t : Tree N L) → map id id t ≡ t
map-id (leaf x)     = refl
map-id (node l v r) = cong₂ (flip node v) (map-id l) (map-id r)
