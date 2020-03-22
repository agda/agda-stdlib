------------------------------------------------------------------------
-- The Agda standard library
--
-- Tree Zipper-related properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary.LeafLabelled.Zipper.Properties where

open import Data.Tree.Binary.LeafLabelled as LT using (LTree; node; leaf)
open import Data.Tree.Binary.LeafLabelled.Zipper
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties
open import Data.List.Base as List using (List ; [] ; _∷_; sum)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.All using (All; just; nothing)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function
open import Level

private
  variable
    a b : Level
    A : Set a
    B : Set b

-- Invariant: Zipper represents a given tree

-- Stability under moving

toTree-up-identity : (zp : Zipper A) → All ((_≡_ on toTree) zp) (up zp)
toTree-up-identity (mkZipper [] foc) = nothing
toTree-up-identity (mkZipper (leftBranch l ∷ ctx) foc) = just refl
toTree-up-identity (mkZipper (rightBranch r ∷ ctx) foc) = just refl

toTree-left-identity : (zp : Zipper A) → All ((_≡_ on toTree) zp) (left zp)
toTree-left-identity (mkZipper ctx (leaf x)) = nothing
toTree-left-identity (mkZipper ctx (node l r)) = just refl

toTree-right-identity : (zp : Zipper A) → All ((_≡_ on toTree) zp) (right zp)
toTree-right-identity (mkZipper ctx (leaf x)) = nothing
toTree-right-identity (mkZipper ctx (node l r)) = just refl

-- Tree-like operations indeed correspond to their counterparts
------------------------------------------------------------------------

toTree-size-commute : ∀ (zp : Zipper A) → size zp ≡ LT.size (toTree zp)
toTree-size-commute (mkZipper c v) = helper c v
  where
    helper : (cs : List (Crumb A))
           → (t : LTree A)
           → size (mkZipper cs t) ≡ LT.size (toTree (mkZipper cs t))
    helper [] foc = +-identityʳ (LT.size foc)
    helper (leftBranch x ∷ ctx) foc = begin
      LT.size foc + (LT.size x + sum (List.map (LT.size ∘ getTree) ctx))  ≡˘⟨ +-assoc (LT.size foc) (LT.size x) (sum (List.map (λ x₁ → LT.size (getTree x₁)) ctx)) ⟩
      LT.size foc + LT.size x + sum (List.map (LT.size ∘ getTree) ctx) ≡⟨ cong (λ y → y + sum (List.map (LT.size ∘ getTree) ctx)) (+-comm (LT.size foc) (LT.size x)) ⟩
      size (mkZipper ctx (node x foc)) ≡⟨ helper ctx (node x foc) ⟩
      LT.size (toTree (mkZipper (leftBranch x ∷ ctx) foc)) ∎
    helper (rightBranch x ∷ ctx) foc = begin
      LT.size foc + (LT.size x + sum (List.map (LT.size ∘ getTree) ctx)) ≡˘⟨ +-assoc (LT.size foc) (LT.size x) (sum (List.map (λ x₁ → LT.size (getTree x₁)) ctx)) ⟩
      LT.size foc + LT.size x + sum (List.map (LT.size ∘ getTree) ctx) ≡⟨ helper ctx (node foc x) ⟩
      LT.size (toTree (mkZipper (rightBranch x ∷ ctx) foc)) ∎

toTree-map-commute : ∀ (f : A → B) zp → toTree (map f zp) ≡ LT.map f (toTree zp)
toTree-map-commute {A = A} f (mkZipper c v) = helper c v
  where
    helper : (cs : List (Crumb A))
           → (t : LTree A)
           → toTree (map f (mkZipper cs t)) ≡ LT.map f (toTree (mkZipper cs t))
    helper [] foc = refl
    helper (leftBranch x ∷ ctx) foc = helper ctx (node x foc)
    helper (rightBranch x ∷ ctx) foc = helper ctx (node foc x)

toTree-foldr-commute : ∀ (f : B → B → B) (g : A → B) zp → foldr f g zp ≡ LT.foldr f g (toTree zp)
toTree-foldr-commute {B = B} {A = A} f g (mkZipper c v) = helper c v
  where
    helper : (cs : List (Crumb A))
           → (t : LTree A)
           → foldr f g (mkZipper cs t) ≡ LT.foldr f g (toTree (mkZipper cs t))
    helper [] foc = refl
    helper (leftBranch x ∷ ctx) foc = helper ctx (node x foc)
    helper (rightBranch x ∷ ctx) foc = helper ctx (node foc x)
