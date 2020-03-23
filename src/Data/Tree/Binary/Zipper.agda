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
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

data Crumb (A : Set a) (B : Set b) : Set (a ⊔ b) where
  leftBranch : A → Tree A B → Crumb A B
  rightBranch : A → Tree A B → Crumb A B

record Zipper (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor mkZipper
  field
    context : List (Crumb A B)
    focus : Tree A B

open Zipper public

-- Fundamental operations of a Zipper: Moving around
------------------------------------------------------------------------

up : Zipper A B → Maybe (Zipper A B)
up (mkZipper [] foc) = nothing
up (mkZipper (leftBranch m l ∷ ctx) foc) = just $ mkZipper ctx (node l m foc)
up (mkZipper (rightBranch m r ∷ ctx) foc) = just $ mkZipper ctx (node foc m r)

left : Zipper A B → Maybe (Zipper A B)
left (mkZipper ctx (leaf x)) = nothing
left (mkZipper ctx (node l m r)) = just $ mkZipper (rightBranch m r ∷ ctx) l

right : Zipper A B → Maybe (Zipper A B)
right (mkZipper ctx (leaf x)) = nothing
right (mkZipper ctx (node l m r)) = just $ mkZipper (leftBranch m l ∷ ctx) r

-- To and from trees
------------------------------------------------------------------------

plug : List (Crumb A B) → Tree A B → Tree A B
plug [] t = t
plug (leftBranch m l ∷ xs) t = plug xs (node l m t)
plug (rightBranch m r ∷ xs) t = plug xs (node t m r)

toTree : Zipper A B → Tree A B
toTree (mkZipper ctx foc) = plug ctx foc

fromTree : Tree A B → Zipper A B
fromTree = mkZipper []

-- Tree-like operations
------------------------------------------------------------------------

getTree : Crumb A B → Tree A B
getTree (leftBranch m x) = x
getTree (rightBranch m x) = x

mapCrumb : (A → C) → (B → D) → Crumb A B → Crumb C D
mapCrumb f g (leftBranch m x) = leftBranch (f m) (BT.map f g x)
mapCrumb f g (rightBranch m x) = rightBranch (f m) (BT.map f g x)

#nodes : Zipper A B → ℕ
#nodes (mkZipper ctx foc) = BT.#nodes foc + sum (List.map (suc ∘ BT.#nodes ∘ getTree) ctx)

#leaves : Zipper A B → ℕ
#leaves (mkZipper ctx foc) = BT.#leaves foc + sum (List.map (BT.#leaves ∘ getTree) ctx)

map : (A → C) → (B → D) → Zipper A B → Zipper C D
map f g (mkZipper ctx foc) = mkZipper (List.map (mapCrumb f g) ctx) (BT.map f g foc)

foldr : (C → A → C → C) → (B → C) → Zipper A B → C
foldr {C = C} {A = A} {B = B} f g (mkZipper ctx foc) = List.foldl step (BT.foldr f g foc) ctx
  where
    step : C → Crumb A B → C
    step val (leftBranch m x) = f (BT.foldr f g x) m val
    step val (rightBranch m x) = f val m (BT.foldr f g x)

-- Attach nodes to the top most part of the zipper
------------------------------------------------------------------------

attach : Zipper A B → List (Crumb A B) → Zipper A B
attach (mkZipper ctx foc) xs = mkZipper (ctx ++ xs) foc

infixr 5 _⟪_⟫ˡ_
infixl 5 _⟪_⟫ʳ_

_⟪_⟫ˡ_ : Tree A B → A → Zipper A B → Zipper A B
l ⟪ m ⟫ˡ zp = attach zp [ leftBranch m l ]

_⟪_⟫ʳ_ : Zipper A B → A → Tree A B → Zipper A B
zp ⟪ m ⟫ʳ r = attach zp [ rightBranch m r ]
