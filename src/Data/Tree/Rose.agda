------------------------------------------------------------------------
-- The Agda standard library
--
-- Rose trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Data.Tree.Rose where

open import Level using (Level)
open import Size
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕₚ
open import Data.List.Extrema.Nat
open import Function.Base using (_∘_)

private
  variable
    a b : Level
    A : Set a
    B : Set b
    i : Size

------------------------------------------------------------------------
-- Type and basic constructions

data Rose (A : Set a) : Size → Set a where
  node : (a : A) (ts : List (Rose A i)) → Rose A (↑ i)

leaf : A → Rose A ∞
leaf a = node a []

------------------------------------------------------------------------
-- Transforming rose trees

map : (A → B) → Rose A i → Rose B i
map f (node a ts) = node (f a) (List.map (map f) ts)

------------------------------------------------------------------------
-- Reducing rose trees

foldr : (A → List B → B) → Rose A i → B
foldr n (node a ts) = n a (List.map (foldr n) ts)

depth : Rose A i → ℕ
depth (node a ts) = suc (max 0 (List.map depth ts))
