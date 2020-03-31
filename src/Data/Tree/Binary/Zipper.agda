------------------------------------------------------------------------
-- The Agda standard library
--
-- Zippers for Binary Trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary.Zipper where

open import Level using (Level; _⊔_)
open import Data.Tree.Binary as BT using (Tree; node; leaf)
open import Data.List as List using (List; []; _∷_; sum; _++_; [_])
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Function

private
  variable
    a n n₁ l l₁ : Level
    A : Set a
    N : Set n
    N₁ : Set n₁
    L : Set l
    L₁ : Set l₁

data Crumb (N : Set n) (L : Set l) : Set (n ⊔ l) where
  leftBranch : N → Tree N L → Crumb N L
  rightBranch : N → Tree N L → Crumb N L

record Zipper (N : Set n) (L : Set l) : Set (n ⊔ l) where
  constructor mkZipper
  field
    context : List (Crumb N L)
    focus : Tree N L

open Zipper public

------------------------------------------------------------------------
-- Fundamental operations of a Zipper: Moving around

up : Zipper N L → Maybe (Zipper N L)
up (mkZipper [] foc) = nothing
up (mkZipper (leftBranch m l ∷ ctx) foc) = just $ mkZipper ctx (node l m foc)
up (mkZipper (rightBranch m r ∷ ctx) foc) = just $ mkZipper ctx (node foc m r)

left : Zipper N L → Maybe (Zipper N L)
left (mkZipper ctx (leaf x)) = nothing
left (mkZipper ctx (node l m r)) = just $ mkZipper (rightBranch m r ∷ ctx) l

right : Zipper N L → Maybe (Zipper N L)
right (mkZipper ctx (leaf x)) = nothing
right (mkZipper ctx (node l m r)) = just $ mkZipper (leftBranch m l ∷ ctx) r

------------------------------------------------------------------------
-- To and from trees

plug : List (Crumb N L) → Tree N L → Tree N L
plug [] t = t
plug (leftBranch m l ∷ xs) t = plug xs (node l m t)
plug (rightBranch m r ∷ xs) t = plug xs (node t m r)

toTree : Zipper N L → Tree N L
toTree (mkZipper ctx foc) = plug ctx foc

fromTree : Tree N L → Zipper N L
fromTree = mkZipper []

------------------------------------------------------------------------
-- Tree-like operations

getTree : Crumb N L → Tree N L
getTree (leftBranch m x) = x
getTree (rightBranch m x) = x

mapCrumb : (N → N₁) → (L → L₁) → Crumb N L → Crumb N₁ L₁
mapCrumb f g (leftBranch m x) = leftBranch (f m) (BT.map f g x)
mapCrumb f g (rightBranch m x) = rightBranch (f m) (BT.map f g x)

#nodes : Zipper N L → ℕ
#nodes (mkZipper ctx foc) = BT.#nodes foc + sum (List.map (suc ∘ BT.#nodes ∘ getTree) ctx)

#leaves : Zipper N L → ℕ
#leaves (mkZipper ctx foc) = BT.#leaves foc + sum (List.map (BT.#leaves ∘ getTree) ctx)

map : (N → N₁) → (L → L₁) → Zipper N L → Zipper N₁ L₁
map f g (mkZipper ctx foc) = mkZipper (List.map (mapCrumb f g) ctx) (BT.map f g foc)

foldr : (A → N → A → A) → (L → A) → Zipper N L → A
foldr {A = A} {N = N} {L = L} f g (mkZipper ctx foc) = List.foldl step (BT.foldr f g foc) ctx
  where
    step : A → Crumb N L → A
    step val (leftBranch m x) = f (BT.foldr f g x) m val
    step val (rightBranch m x) = f val m (BT.foldr f g x)

------------------------------------------------------------------------
-- Attach nodes to the top most part of the zipper

attach : Zipper N L → List (Crumb N L) → Zipper N L
attach (mkZipper ctx foc) xs = mkZipper (ctx ++ xs) foc

infixr 5 _⟪_⟫ˡ_
infixl 5 _⟪_⟫ʳ_

_⟪_⟫ˡ_ : Tree N L → N → Zipper N L → Zipper N L
l ⟪ m ⟫ˡ zp = attach zp [ leftBranch m l ]

_⟪_⟫ʳ_ : Zipper N L → N → Tree N L → Zipper N L
zp ⟪ m ⟫ʳ r = attach zp [ rightBranch m r ]
