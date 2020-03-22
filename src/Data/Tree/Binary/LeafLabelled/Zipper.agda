------------------------------------------------------------------------
-- The Agda standard library
--
-- Zippers for Binary Trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary.LeafLabelled.Zipper where

open import Level
open import Data.Tree.Binary.LeafLabelled as LT using (LTree; node; leaf)
open import Data.List as List using (List; []; _∷_; sum)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; _+_)
open import Function

private
  variable
    a b : Level
    A : Set a
    B : Set b

data Crumb (A : Set a) : Set a where
  leftBranch : LTree A → Crumb A
  rightBranch : LTree A → Crumb A

record Zipper (A : Set a) : Set a where
  constructor mkZipper
  field
    context : List (Crumb A)
    focus : LTree A


open Zipper public

-- Fundamental operations of a Zipper: Moving around
------------------------------------------------------------------------

up : Zipper A → Maybe (Zipper A)
up (mkZipper [] foc) = nothing
up (mkZipper (leftBranch l ∷ ctx) foc) = just $ mkZipper ctx (node l foc)
up (mkZipper (rightBranch r ∷ ctx) foc) = just $ mkZipper ctx (node foc r)

left : Zipper A → Maybe (Zipper A)
left (mkZipper ctx (leaf x)) = nothing
left (mkZipper ctx (node l r)) = just $ mkZipper (rightBranch r ∷ ctx) l

right : Zipper A → Maybe (Zipper A)
right (mkZipper ctx (leaf x)) = nothing
right (mkZipper ctx (node l r)) = just $ mkZipper (leftBranch l ∷ ctx) r

-- To and from trees
------------------------------------------------------------------------

toTreeHelper : List (Crumb A) → LTree A → LTree A
toTreeHelper [] t = t
toTreeHelper (leftBranch l ∷ xs) t = toTreeHelper xs (node l t)
toTreeHelper (rightBranch r ∷ xs) t = toTreeHelper xs (node t r)

toTree : Zipper A → LTree A
toTree (mkZipper ctx foc) = toTreeHelper ctx foc


fromTree : LTree A → Zipper A
fromTree = mkZipper []

-- Tree-like operations
------------------------------------------------------------------------

getTree : Crumb A → LTree A
getTree (leftBranch x) = x
getTree (rightBranch x) = x

mapCrumb : (A → B) → Crumb A → Crumb B
mapCrumb f (leftBranch x) = leftBranch (LT.map f x)
mapCrumb f (rightBranch x) = rightBranch (LT.map f x)

size : Zipper A → ℕ
size (mkZipper ctx foc) = LT.size foc + sum (List.map (LT.size ∘ getTree) ctx)

map : (A → B) → Zipper A → Zipper B
map f (mkZipper ctx foc) = mkZipper (List.map (mapCrumb f) ctx) (LT.map f foc)

foldr : (B → B → B) → (A → B) → Zipper A → B
foldr {B = B} {A = A} f g (mkZipper ctx foc) = List.foldl step (LT.foldr f g foc) ctx
  where
    step : B → Crumb A → B
    step val (leftBranch x) = f (LT.foldr f g x) val
    step val (rightBranch x) = f val (LT.foldr f g x)
