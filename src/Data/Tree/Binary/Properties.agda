------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of binary trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary.Properties where

open import Function using (_∘_)
open import Function.Nary.NonDependent using (congₙ)
open import Level using (Level)
open import Data.Nat.Base using (suc; _+_)
open import Data.Tree.Binary
open import Function.Base
open import Relation.Binary.PropositionalEquality

private
  variable
    a n n₁ n₂ l l₁ l₂ : Level
    A : Set a
    N : Set n
    N₁ : Set n₁
    N₂ : Set n₂
    L : Set l
    L₁ : Set l₁
    L₂ : Set l₂

#nodes-map : ∀ (f : N → N₁) (g : L → L₁) t → #nodes (map f g t) ≡ #nodes t
#nodes-map f g (leaf x)     = refl
#nodes-map f g (node l m r) =
  cong₂ (λ l r → l + suc r) (#nodes-map f g l) (#nodes-map f g r)

#nodes-mapₙ : ∀ (f : N → N₁) (t : Tree N L) → #nodes (mapₙ f t) ≡ #nodes t
#nodes-mapₙ f = #nodes-map f id

#nodes-mapₗ : ∀ (g : L → L₁) (t : Tree N L) → #nodes (mapₗ g t) ≡ #nodes t
#nodes-mapₗ = #nodes-map id

#leaves-map : ∀ (f : N → N₁) (g : L → L₁) t → #leaves (map f g t) ≡ #leaves t
#leaves-map f g (leaf x)     = refl
#leaves-map f g (node l m r) =
  cong₂ _+_ (#leaves-map f g l) (#leaves-map f g r)

#leaves-mapₙ : ∀ (f : N → N₁) (t : Tree N L) → #leaves (mapₙ f t) ≡ #leaves t
#leaves-mapₙ f = #leaves-map f id

#leaves-mapₗ : ∀ (g : L → L₁) (t : Tree N L) → #leaves (mapₗ g t) ≡ #leaves t
#leaves-mapₗ = #leaves-map id

map-id : ∀ (t : Tree N L) → map id id t ≡ t
map-id (leaf x)     = refl
map-id (node l v r) = cong₂ (flip node v) (map-id l) (map-id r)

map-compose : ∀ {f₁ : N₁ → N₂} {f₂ : N → N₁} {g₁ : L₁ → L₂} {g₂ : L → L₁} →
              map (f₁ ∘ f₂) (g₁ ∘ g₂) ≗ map f₁ g₁ ∘ map f₂ g₂
map-compose (leaf x) = refl
map-compose (node l v r) = cong₂ (λ l r → node l _ r) (map-compose l) (map-compose r)

map-cong : ∀ {f₁ f₂ : N → N₁} {g₁ g₂ : L → L₁} → f₁ ≗ f₂ → g₁ ≗ g₂ → map f₁ g₁ ≗ map f₂ g₂
map-cong p q (leaf x) = cong leaf (q x)
map-cong p q (node l v r) = congₙ 3 node (map-cong p q l) (p v) (map-cong p q r)
