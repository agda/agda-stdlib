------------------------------------------------------------------------
-- The Agda standard library
--
-- Simple implementation of sets of ℕ.
--
-- Since ℕ is represented as unary numbers, simply having an ordered list of
-- numbers to represent a set is quite inefficient. For instance, to see if
-- 6 is in the set {1, 3, 4}, we have to do a comparison with 1, then 3, and
-- then 4. But 4 is equal to suc 3, so we should be able to share the work
-- accross those two comparisons.
--
-- This module defines a type that represents {1, 3, 4} as:
--
--   1 ∷ 1 ∷ 0 ∷ []
--
-- i.e. we only store the gaps. When checking if a number (the needle) is in the
-- set (the haystack), we subtract each successive member of the haystack from the
-- needle as we go. For example, to check if 6 is in the above set, we do the
-- following:
--
--   start:                  6 ∈? (1 ∷ 1 ∷ 0 ∷ [])
--   test head:              6 ≟ 1
--   not equal, so continue: (6 - 1 - 1) ∈? (1 ∷ 0 ∷ [])
--   compute:                4 ∈? (1 ∷ 0 ∷ [])
--   test head:              4 ≟ 1
--   not equal, so continue: (4 - 1 - 1) ∈? (0 ∷ [])
--   compute:                2 ∈? (0 ∷ [])
--   test head:              2 ≟ 0
--   not equal, so continue: (2 - 1 - 1) ∈? []
--   empty list:             false
--
-- In this way, we change the membership test from O(n²) to O(n).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Tactic.RingSolver.Core.NatSet where

open import Data.Nat   as ℕ     using (ℕ; suc; zero)
open import Data.List  as List  using (List; _∷_; [])
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Bool  as Bool  using (Bool)
open import Function
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Helper methods

para : ∀ {a b} {A : Set a} {B : Set b} →
       (A → List A → B → B) → B → List A → B
para f b []       = b
para f b (x ∷ xs) = f x xs (para f b xs)

------------------------------------------------------------------------
-- Definition

NatSet : Set
NatSet = List ℕ

------------------------------------------------------------------------
-- Functions

insert : ℕ → NatSet → NatSet
insert x xs = para f (_∷ []) xs x
  where
  f : ℕ → NatSet → (ℕ → NatSet) → ℕ → NatSet
  f y ys c x with ℕ.compare x y
  ... | ℕ.less x k    = x ∷ k ∷ ys
  ... | ℕ.equal x     = x ∷ ys
  ... | ℕ.greater y k = y ∷ c k

delete : ℕ → NatSet → NatSet
delete x xs = para f (const []) xs x
  where
  f : ℕ → NatSet → (ℕ → NatSet) → ℕ → NatSet
  f y ys c x with ℕ.compare x y
  f y ys c x         | ℕ.less    x k = y ∷ ys
  f y [] c x         | ℕ.equal   x   = []
  f y₁ (y₂ ∷ ys) c x | ℕ.equal   x   = suc x ℕ.+ y₂ ∷ ys
  f y ys c x         | ℕ.greater y k = y ∷ c k

-- Returns the position of the element, if it's present.
lookup : ℕ → NatSet → Maybe ℕ
lookup x xs = List.foldr f (const (const nothing)) xs x 0
  where
  f : ℕ → (ℕ → ℕ → Maybe ℕ) → ℕ → ℕ → Maybe ℕ
  f y ys x i with ℕ.compare x y
  ... | ℕ.less     x k = nothing
  ... | ℕ.equal    y   = just i
  ... | ℕ.greater  y k = ys k (suc i)


member : ℕ → NatSet → Bool
member x = Maybe.is-just ∘ lookup x

fromList : List ℕ → NatSet
fromList = List.foldr insert []

toList : NatSet → List ℕ
toList = List.drop 1 ∘ List.map ℕ.pred ∘ List.scanl (λ x y → suc (y ℕ.+ x)) 0

------------------------------------------------------------------------
-- Tests

private
  example₁ : fromList (4 ∷ 3 ∷ 1 ∷ 0 ∷ 2 ∷ []) ≡ (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
  example₁ = refl

  example₂ : lookup 3 (fromList (4 ∷ 3 ∷ 1 ∷ 0 ∷ 2 ∷ [])) ≡ just 3
  example₂ = refl

  example₃ : toList (fromList (4 ∷ 3 ∷ 1 ∷ 0 ∷ 2 ∷ [])) ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  example₃ = refl

  example₄ : delete 3 (fromList (4 ∷ 3 ∷ 1 ∷ 2 ∷ [])) ≡ fromList (4 ∷ 1 ∷ 2 ∷ [])
  example₄ = refl

  example₅ : delete 3 (fromList (4 ∷ 1 ∷ 2 ∷ [])) ≡ fromList (4 ∷ 1 ∷ 2 ∷ [])
  example₅ = refl
