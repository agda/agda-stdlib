------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of binary trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary.Properties where

open import Level using (Level)
open import Data.Nat.Base using (suc; _+_)
open import Data.Tree.Binary
open import Function.Base
open import Relation.Binary.PropositionalEquality

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

#nodes-map : ∀ (f : A → B) (g : C → D) t → #nodes (map f g t) ≡ #nodes t
#nodes-map f g (leaf x)     = refl
#nodes-map f g (node l m r) =
  cong₂ (λ l r → l + suc r) (#nodes-map f g l) (#nodes-map f g r)

#leaves-map : ∀ (f : A → B) (g : C → D) t → #leaves (map f g t) ≡ #leaves t
#leaves-map f g (leaf x)     = refl
#leaves-map f g (node l m r) =
  cong₂ _+_ (#leaves-map f g l) (#leaves-map f g r)

map-id : ∀ (t : Tree A B) → map id id t ≡ t
map-id (leaf x)     = refl
map-id (node l v r) = cong₂ (flip node v) (map-id l) (map-id r)
