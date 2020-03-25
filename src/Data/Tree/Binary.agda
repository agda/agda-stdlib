------------------------------------------------------------------------
-- The Agda standard library
--
-- Binary Trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary where

open import Level using (Level; _⊔_)
open import Data.List.Base using (List)
open import Data.DifferenceList as DiffList using (DiffList; []; _∷_; _∷ʳ_; _++_; [_])
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Function.Base

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

data Tree (A : Set a) (B : Set b) : Set (a ⊔ b) where
  leaf : B → Tree A B
  node : Tree A B → A → Tree A B → Tree A B

map : (A → C) → (B → D) → Tree A B → Tree C D
map f g (leaf x)     = leaf (g x)
map f g (node l m r) = node (map f g l) (f m) (map f g r)

map₁ : (A → C) → Tree A B → Tree C B
map₁ f t = map f id t

map₂ : (B → C) → Tree A B → Tree A C
map₂ f t = map id f t

#nodes : Tree A B → ℕ
#nodes (leaf x)     = 0
#nodes (node l m r) = #nodes l + suc (#nodes r)

#leaves : Tree A B → ℕ
#leaves (leaf x)     = 1
#leaves (node l m r) = #leaves l + #leaves r

foldr : (C → A → C → C) → (B → C) → Tree A B → C
foldr f g (leaf x)     = g x
foldr f g (node l m r) = f (foldr f g l) m (foldr f g r)

------------------------------------------------------------------------
-- Extraction to lists, depth first and left to right.

module Prefix where

  toDiffList : Tree A B → DiffList A
  toDiffList = foldr (λ l m r → m ∷ l ++ r) (λ _ → [])

  toList : Tree A B → List A
  toList = DiffList.toList ∘′ toDiffList

module Infix where

  toDiffList : Tree A B → DiffList A
  toDiffList = foldr (λ l m r → l ++ m ∷ r) (λ _ → [])

  toList : Tree A B → List A
  toList = DiffList.toList ∘′ toDiffList

module Suffix where

  toDiffList : Tree A B → DiffList A
  toDiffList = foldr (λ l m r → l ++ r ∷ʳ m) (λ _ → [])

  toList : Tree A B → List A
  toList = DiffList.toList ∘′ toDiffList

module Leaves where

  toDiffList : Tree A B → DiffList B
  toDiffList (leaf x) = [ x ]
  toDiffList (node l m r) = toDiffList l ++ toDiffList r

  toList : Tree A B → List B
  toList = DiffList.toList ∘′ toDiffList
