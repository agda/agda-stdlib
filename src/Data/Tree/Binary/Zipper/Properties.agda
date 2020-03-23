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
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

-- Invariant: Zipper represents a given tree

-- Stability under moving

toTree-up-identity : (zp : Zipper A B) → All ((_≡_ on toTree) zp) (up zp)
toTree-up-identity (mkZipper [] foc) = nothing
toTree-up-identity (mkZipper (leftBranch m l ∷ ctx) foc) = just refl
toTree-up-identity (mkZipper (rightBranch m r ∷ ctx) foc) = just refl

toTree-left-identity : (zp : Zipper A B) → All ((_≡_ on toTree) zp) (left zp)
toTree-left-identity (mkZipper ctx (leaf x)) = nothing
toTree-left-identity (mkZipper ctx (node l m r)) = just refl

toTree-right-identity : (zp : Zipper A B) → All ((_≡_ on toTree) zp) (right zp)
toTree-right-identity (mkZipper ctx (leaf x)) = nothing
toTree-right-identity (mkZipper ctx (node l m r)) = just refl

-- Tree-like operations indeed correspond to their counterparts
------------------------------------------------------------------------

toTree-#nodes-commute : ∀ (zp : Zipper A B) → #nodes zp ≡ BT.#nodes (toTree zp)
toTree-#nodes-commute (mkZipper c v) = helper c v
  where
    helper : (cs : List (Crumb A B))
           → (t : Tree A B)
           → #nodes (mkZipper cs t) ≡ BT.#nodes (toTree (mkZipper cs t))
    helper [] foc = +-identityʳ (BT.#nodes foc)
    helper (leftBranch m l ∷ ctx) foc = let
      x = sum (List.map (suc ∘ BT.#nodes ∘ getTree) ctx) in begin
      BT.#nodes foc + (1 + (BT.#nodes l + x)) ≡˘⟨ +-assoc (BT.#nodes foc) 1 (BT.#nodes l + x) ⟩
      BT.#nodes foc + 1 + (BT.#nodes l + x)   ≡⟨ cong (λ y → y + (BT.#nodes l + x)) (+-comm (BT.#nodes foc) 1) ⟩
      1 + BT.#nodes foc + (BT.#nodes l + x)   ≡˘⟨ +-assoc (1 + BT.#nodes foc) (BT.#nodes l) x ⟩
      1 + BT.#nodes foc + BT.#nodes l + x     ≡⟨ cong (λ y → y + x) (+-comm (1 + BT.#nodes foc) (BT.#nodes l)) ⟩
      #nodes (mkZipper ctx (node l m foc))    ≡⟨ helper ctx (node l m foc) ⟩
      BT.#nodes (toTree (mkZipper (leftBranch m l ∷ ctx) foc)) ∎
    helper (rightBranch m r ∷ ctx) foc = let
      x = sum (List.map (suc ∘ BT.#nodes ∘ getTree) ctx) in begin
      BT.#nodes foc + (1 + (BT.#nodes r + x)) ≡˘⟨ cong (λ y → BT.#nodes foc + y) (+-assoc 1 (BT.#nodes r) (sum (List.map (λ x → suc (BT.#nodes (getTree x))) ctx))) ⟩
      BT.#nodes foc + (1 + BT.#nodes r + x)   ≡˘⟨ +-assoc (BT.#nodes foc) (suc (BT.#nodes r)) x ⟩
      #nodes (mkZipper ctx (node foc m r))    ≡⟨ helper ctx (node foc m r) ⟩
      BT.#nodes (toTree (mkZipper ctx (node foc m r))) ∎

toTree-#leaves-commute : ∀ (zp : Zipper A B) → #leaves zp ≡ BT.#leaves (toTree zp)
toTree-#leaves-commute (mkZipper c v) = helper c v
  where
    helper : (cs : List (Crumb A B))
           → (t : Tree A B)
           → #leaves (mkZipper cs t) ≡ BT.#leaves (toTree (mkZipper cs t))
    helper [] foc = +-identityʳ (BT.#leaves foc)
    helper (leftBranch m l ∷ ctx) foc = let
      x = sum (List.map (BT.#leaves ∘ getTree) ctx) in begin
      BT.#leaves foc + (BT.#leaves l + x)   ≡˘⟨ +-assoc (BT.#leaves foc) (BT.#leaves l) (x) ⟩
      BT.#leaves foc + BT.#leaves l + x     ≡⟨ cong (λ y → y + x) (+-comm (BT.#leaves foc) (BT.#leaves l)) ⟩
      #leaves (mkZipper ctx (node l m foc)) ≡⟨ helper ctx (node l m foc) ⟩
      BT.#leaves (toTree (mkZipper (leftBranch m l ∷ ctx) foc)) ∎
    helper (rightBranch m r ∷ ctx) foc = let
      x = sum (List.map (BT.#leaves ∘ getTree) ctx) in begin
      BT.#leaves foc + (BT.#leaves r + x)   ≡˘⟨ +-assoc (BT.#leaves foc) (BT.#leaves r) (x) ⟩
      #leaves (mkZipper ctx (node foc m r)) ≡⟨ helper ctx (node foc m r) ⟩
      BT.#leaves (toTree (mkZipper (rightBranch m r ∷ ctx) foc)) ∎

toTree-map-commute : ∀ (f : A → C) (g : B → D) zp → toTree (map f g zp) ≡ BT.map f g (toTree zp)
toTree-map-commute {A = A} {B = B} f g (mkZipper c v) = helper c v
  where
    helper : (cs : List (Crumb A B))
           → (t : Tree A B)
           → toTree (map f g (mkZipper cs t)) ≡ BT.map f g (toTree (mkZipper cs t))
    helper [] foc = refl
    helper (leftBranch m l ∷ ctx) foc = helper ctx (node l m foc)
    helper (rightBranch m r ∷ ctx) foc = helper ctx (node foc m r)

toTree-foldr-commute : ∀ (f : C → A → C → C) (g : B → C) zp → foldr f g zp ≡ BT.foldr f g (toTree zp)
toTree-foldr-commute {A = A} {B = B} f g (mkZipper c v) = helper c v
  where
    helper : (cs : List (Crumb A B))
           → (t : Tree A B)
           → foldr f g (mkZipper cs t) ≡ BT.foldr f g (toTree (mkZipper cs t))
    helper [] foc = refl
    helper (leftBranch m l ∷ ctx) foc = helper ctx (node l m foc)
    helper (rightBranch m r ∷ ctx) foc = helper ctx (node foc m r)
