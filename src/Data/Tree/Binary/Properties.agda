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
    a b : Level
    A : Set a
    B : Set b

size-map : ∀ (f : A → B) t → size (map f t) ≡ size t
size-map f leaf         = refl
size-map f (node l m r) =
  cong₂ (λ l r → l + suc r) (size-map f l) (size-map f r)

map-id : ∀ (t : Tree A) → map id t ≡ t
map-id leaf         = refl
map-id (node l v r) = cong₂ (flip node v) (map-id l) (map-id r)
