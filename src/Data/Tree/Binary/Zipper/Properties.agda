------------------------------------------------------------------------
-- The Agda standard library
--
-- Tree Zipper-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary.Zipper.Properties where

open import Data.Tree.Binary as BT using (Tree; node; leaf)
open import Data.Tree.Binary.Zipper
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties
open import Data.List.Base as List using (List ; [] ; _∷_; sum)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.All using (All; just; nothing)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function
open import Level using (Level)

private
  variable
    a n l n₁ l₁ : Level
    A : Set a
    N : Set n
    L : Set l
    N₁ : Set n₁
    L₁ : Set l₁

-- Invariant: Zipper represents a given tree

-- Stability under moving

toTree-up-identity : (zp : Zipper N L) → All ((_≡_ on toTree) zp) (up zp)
toTree-up-identity (mkZipper [] foc) = nothing
toTree-up-identity (mkZipper (leftBranch m l ∷ ctx) foc) = just refl
toTree-up-identity (mkZipper (rightBranch m r ∷ ctx) foc) = just refl

toTree-left-identity : (zp : Zipper N L) → All ((_≡_ on toTree) zp) (left zp)
toTree-left-identity (mkZipper ctx (leaf x)) = nothing
toTree-left-identity (mkZipper ctx (node l m r)) = just refl

toTree-right-identity : (zp : Zipper N L) → All ((_≡_ on toTree) zp) (right zp)
toTree-right-identity (mkZipper ctx (leaf x)) = nothing
toTree-right-identity (mkZipper ctx (node l m r)) = just refl

------------------------------------------------------------------------
-- Tree-like operations indeed correspond to their counterparts

toTree-#nodes-commute : ∀ (zp : Zipper N L) → #nodes zp ≡ BT.#nodes (toTree zp)
toTree-#nodes-commute (mkZipper c v) = helper c v
  where
    helper : (cs : List (Crumb N L)) →
             (t : Tree N L) →
             #nodes (mkZipper cs t) ≡ BT.#nodes (toTree (mkZipper cs t))
    helper [] foc = +-identityʳ (BT.#nodes foc)
    helper cs@(leftBranch m l ∷ ctx) foc = let
      #ctx = sum (List.map (suc ∘ BT.#nodes ∘ getTree) ctx)
      #foc = BT.#nodes foc
      #l = BT.#nodes l in begin
      #foc + (1 + (#l + #ctx))             ≡˘⟨ +-assoc #foc 1 (#l + #ctx) ⟩
      #foc + 1 + (#l + #ctx)               ≡⟨ cong (_+ (#l + #ctx)) (+-comm #foc 1) ⟩
      1 + #foc + (#l + #ctx)               ≡˘⟨ +-assoc (1 + #foc) #l #ctx ⟩
      1 + #foc + #l + #ctx                 ≡⟨ cong (_+ #ctx) (+-comm (1 + #foc) #l) ⟩
      #nodes (mkZipper ctx (node l m foc)) ≡⟨ helper ctx (node l m foc) ⟩
      BT.#nodes (toTree (mkZipper cs foc)) ∎
    helper cs@(rightBranch m r ∷ ctx) foc = let
      #ctx = sum (List.map (suc ∘ BT.#nodes ∘ getTree) ctx)
      #foc = BT.#nodes foc
      #r = BT.#nodes r in begin
      #foc + (1 + (#r + #ctx))             ≡˘⟨ cong (#foc +_) (+-assoc 1 #r #ctx) ⟩
      #foc + (1 + #r + #ctx)               ≡˘⟨ +-assoc #foc (suc #r) #ctx ⟩
      #nodes (mkZipper ctx (node foc m r)) ≡⟨ helper ctx (node foc m r) ⟩
      BT.#nodes (toTree (mkZipper cs foc)) ∎

toTree-#leaves-commute : ∀ (zp : Zipper N L) → #leaves zp ≡ BT.#leaves (toTree zp)
toTree-#leaves-commute (mkZipper c v) = helper c v
  where
    helper : (cs : List (Crumb N L)) →
             (t : Tree N L) →
             #leaves (mkZipper cs t) ≡ BT.#leaves (toTree (mkZipper cs t))
    helper [] foc = +-identityʳ (BT.#leaves foc)
    helper cs@(leftBranch m l ∷ ctx) foc = let
      #ctx = sum (List.map (BT.#leaves ∘ getTree) ctx)
      #foc = BT.#leaves foc
      #l = BT.#leaves l in begin
      #foc + (#l + #ctx)                    ≡˘⟨ +-assoc #foc #l #ctx ⟩
      #foc + #l + #ctx                      ≡⟨ cong (_+ #ctx) (+-comm #foc #l) ⟩
      #leaves (mkZipper ctx (node l m foc)) ≡⟨ helper ctx (node l m foc) ⟩
      BT.#leaves (toTree (mkZipper cs foc)) ∎
    helper cs@(rightBranch m r ∷ ctx) foc = let
      #ctx = sum (List.map (BT.#leaves ∘ getTree) ctx)
      #foc = BT.#leaves foc
      #r = BT.#leaves r in begin
      #foc + (#r + #ctx)                    ≡˘⟨ +-assoc #foc #r #ctx ⟩
      #leaves (mkZipper ctx (node foc m r)) ≡⟨ helper ctx (node foc m r) ⟩
      BT.#leaves (toTree (mkZipper cs foc)) ∎

toTree-map-commute : ∀ (f : N → N₁) (g : L → L₁) zp → toTree (map f g zp) ≡ BT.map f g (toTree zp)
toTree-map-commute {N = N} {L = L} f g (mkZipper c v) = helper c v
  where
    helper : (cs : List (Crumb N L)) →
             (t : Tree N L) →
             toTree (map f g (mkZipper cs t)) ≡ BT.map f g (toTree (mkZipper cs t))
    helper [] foc = refl
    helper (leftBranch m l ∷ ctx) foc = helper ctx (node l m foc)
    helper (rightBranch m r ∷ ctx) foc = helper ctx (node foc m r)

toTree-foldr-commute : ∀ (f : A → N → A → A) (g : L → A) zp → foldr f g zp ≡ BT.foldr f g (toTree zp)
toTree-foldr-commute {N = N} {L = L} f g (mkZipper c v) = helper c v
  where
    helper : (cs : List (Crumb N L)) →
             (t : Tree N L) →
             foldr f g (mkZipper cs t) ≡ BT.foldr f g (toTree (mkZipper cs t))
    helper [] foc = refl
    helper (leftBranch m l ∷ ctx) foc = helper ctx (node l m foc)
    helper (rightBranch m r ∷ ctx) foc = helper ctx (node foc m r)

------------------------------------------------------------------------
-- Properties of the building functions

-- _⟪_⟫ˡ_ properties

toTree-⟪⟫ˡ-commute : ∀ l m (zp : Zipper N L) → toTree (l ⟪ m ⟫ˡ zp) ≡ node l m (toTree zp)
toTree-⟪⟫ˡ-commute {N = N} {L = L} l m (mkZipper c v) = helper c v
  where
    helper : (cs : List (Crumb N L)) →
             (t : Tree N L) →
             toTree (l ⟪ m ⟫ˡ mkZipper cs t) ≡ node l m (toTree $ mkZipper cs t)
    helper [] foc = refl
    helper (leftBranch m l ∷ ctx) foc = helper ctx (node l m foc)
    helper (rightBranch m r ∷ ctx) foc = helper ctx (node foc m r)

-- _⟪_⟫ʳ_ properties

toTree-⟪⟫ʳ-commute : ∀ (zp : Zipper N L) m r → toTree (zp ⟪ m ⟫ʳ r) ≡ node (toTree zp) m r
toTree-⟪⟫ʳ-commute {N = N} {L = L} (mkZipper c v) m r = helper c v
  where
    helper : (cs : List (Crumb N L)) →
             (t : Tree N L) →
             toTree (mkZipper cs t ⟪ m ⟫ʳ r) ≡ node (toTree $ mkZipper cs t) m r
    helper [] foc = refl
    helper (leftBranch m l ∷ ctx) foc = helper ctx (node l m foc)
    helper (rightBranch m r ∷ ctx) foc = helper ctx (node foc m r)
