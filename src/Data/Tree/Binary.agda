------------------------------------------------------------------------
-- The Agda standard library
--
-- Binary Trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Data.Tree.Binary where

open import Level using (Level; _⊔_)
open import Size
open import Data.List.Base as List using (List; fromMaybe)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.DifferenceList as DiffList using (DiffList; []; _∷_; _∷ʳ_; _++_; [_])
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Tree.Rose as Rose using (Rose; node)
open import Function.Base

private
  variable
    n l n₁ l₁ a : Level
    N : Set n
    L : Set l
    N₁ : Set n₁
    L₁ : Set l₁
    A B : Set a
    i : Size

-- Trees with node values of type N and leaf values of type L
data Tree (N : Set n) (L : Set l) : Set (n ⊔ l) where
  leaf : L → Tree N L
  node : Tree N L → N → Tree N L → Tree N L

map : (N → N₁) → (L → L₁) → Tree N L → Tree N₁ L₁
map f g (leaf x)     = leaf (g x)
map f g (node l m r) = node (map f g l) (f m) (map f g r)

mapₙ : (N → N₁) → Tree N L → Tree N₁ L
mapₙ f t = map f id t

mapₗ : (L → L₁) → Tree N L → Tree N L₁
mapₗ f t = map id f t

#nodes : Tree N L → ℕ
#nodes (leaf x)     = 0
#nodes (node l m r) = #nodes l + suc (#nodes r)

#leaves : Tree N L → ℕ
#leaves (leaf x)     = 1
#leaves (node l m r) = #leaves l + #leaves r

foldr : (A → N → A → A) → (L → A) → Tree N L → A
foldr f g (leaf x)     = g x
foldr f g (node l m r) = f (foldr f g l) m (foldr f g r)

------------------------------------------------------------------------
-- Conversion to Rose trees

toRose : Tree A → Rose (Maybe A) ∞
toRose leaf         = node nothing List.[]
toRose (node l a r) = node (just a) (toRose l ∷ toRose r ∷ [])
  where open List.List

------------------------------------------------------------------------
-- Extraction to lists, depth first and left to right.

module Prefix where

  toDiffList : Tree A → DiffList A
  toDiffList = foldr (λ l m r → m ∷ l ++ r) []

  toList : Tree N L → List N
  toList = DiffList.toList ∘′ toDiffList

module Infix where

  toDiffList : Tree A → DiffList A
  toDiffList = foldr (λ l m r → l ++ m ∷ r) []

  toList : Tree N L → List N
  toList = DiffList.toList ∘′ toDiffList

module Suffix where

  toDiffList : Tree N L → DiffList N
  toDiffList = foldr (λ l m r → l ++ r ∷ʳ m) []

  toList : Tree N L → List N
  toList = DiffList.toList ∘′ toDiffList

module Leaves where

  toDiffList : Tree N L → DiffList L
  toDiffList (leaf x) = [ x ]
  toDiffList (node l m r) = toDiffList l ++ toDiffList r

  toList : Tree N L → List L
  toList = DiffList.toList ∘′ toDiffList
