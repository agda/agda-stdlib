------------------------------------------------------------------------
-- The Agda standard library
--
-- Rose trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Data.Tree.Rose where

open import Level using (Level)
open import Size
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.List.Extrema.Nat
import Data.Tree.Binary as Bin
open import Function.Base using (_∘_)

private
  variable
    a : Level
    A B C : Set a
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

------------------------------------------------------------------------
-- Conversion from binary trees

module _ (fromNode : A → C) (fromLeaf : B → C) where

  fromBinary : Bin.Tree A B → Rose C ∞
  fromBinary (Bin.leaf x)     = node (fromLeaf x) []
  fromBinary (Bin.node l x r) = node (fromNode x)
    (fromBinary l ∷ fromBinary r ∷ [])
