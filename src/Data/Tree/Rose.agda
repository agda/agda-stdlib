------------------------------------------------------------------------
-- The Agda standard library
--
-- Rose trees, without sized types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Rose where

open import Data.List.Base as List using (List; []; _∷_; [_]; _++_)
open import Data.List.Extrema.Nat using (max)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Tree.Binary as Tree using (Tree)
open import Function.Base using (const; _∘′_; _$_)
open import Level using (Level)

private
  variable
    a : Level
    A B C : Set a


------------------------------------------------------------------------
-- Type and basic constructions

data Rose (A : Set a) : Set a where
  node : (a : A) (ts : List (Rose A)) → Rose A

pattern leaf a = node a []

pure : A → Rose A
pure = leaf

------------------------------------------------------------------------
-- Transforming rose trees

module _ (f : A → B) where

  map : Rose A → Rose B
  map = λ where (node a ts) → node (f a) (mapList ts)
    module Map where
    mapList : List (Rose A) → List (Rose B)
    mapList []       = []
    mapList (t ∷ ts) = map t ∷ mapList ts


------------------------------------------------------------------------
-- Reducing rose trees

module _ (n : A → List B → B) where

  foldr : Rose A → B
  foldr = λ where (node a ts) → n a (foldrList ts)
    module Foldr where
    foldrList : List (Rose A) → List B
    foldrList []       = []
    foldrList (t ∷ ts) = foldr t ∷ foldrList ts

depth : Rose A → ℕ
depth = foldr $ const (suc ∘′ max zero)


------------------------------------------------------------------------
-- Conversion from binary trees

module _ (fromNode : A → C) (fromLeaf : B → C) where

  fromBinary : Tree A B → Rose C
  fromBinary (Tree.leaf x)     = leaf (fromLeaf x)
  fromBinary (Tree.node l x r) = node (fromNode x) $
    [ fromBinary l ] ++ [ fromBinary r ]
