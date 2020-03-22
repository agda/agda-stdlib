------------------------------------------------------------------------
-- The Agda standard library
--
-- Binary Trees with Labelled Leaves
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary.LeafLabelled where

open import Level
open import Data.Nat.Base using (ℕ; _+_)
open import Data.List using (List; [_]; _++_)


private
  variable
    a b : Level
    A : Set a
    B : Set b

data LTree (A : Set a) : Set a where
  leaf : A → LTree A
  node : LTree A → LTree A → LTree A

map : (A → B) → LTree A → LTree B
map f (leaf x) = leaf (f x)
map f (node l r) = node (map f l) (map f r)

size : LTree A → ℕ
size (leaf x) = 1
size (node l r) = size l + size r

foldr : (B → B → B) → (A → B) → LTree A → B
foldr f g (leaf x) = g x
foldr f g (node l r) = f (foldr f g l) (foldr f g r)

------------------------------------------------------------------------
-- Extraction to lists

toList : LTree A → List A
toList (leaf x) = [ x ]
toList (node l r) = toList l ++ toList r
