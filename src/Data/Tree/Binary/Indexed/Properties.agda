

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
    i : 𝕋


#nodes-map : ∀ (f : N → N₁) (g : L → L₁) (t : ITree N L i) → #nodes (map f g t) ≡ #nodes t
#nodes-map f g t = refl

#nodes-mapₙ : ∀ (f : N → N₁) (t : ITree N L i) → #nodes (mapₙ f t) ≡ #nodes t
#nodes-mapₙ f t = refl

#nodes-mapₗ : ∀ (g : L → L₁) (t : ITree N L i) → #nodes (mapₗ g t) ≡ #nodes t
#nodes-mapₗ g t = refl

#leaves-map : ∀ (f : N → N₁) (g : L → L₁) (t : ITree N L i) → #leaves (map f g t) ≡ #leaves t
#leaves-map f g t = refl

#leaves-mapₙ : ∀ (f : N → N₁) (t : ITree N L i) → #leaves (mapₙ f t) ≡ #leaves t
#leaves-mapₙ f t = refl

#leaves-mapₗ : ∀ (g : L → L₁) (t : ITree N L i) → #leaves (mapₗ g t) ≡ #leaves t
#leaves-mapₗ g t = refl

map-id : ∀ (t : ITree N L i) → map id id t ≡ t
map-id (leaf x) = refl
map-id (node l m r) = cong₂ (flip node m) (map-id l) (map-id r)
