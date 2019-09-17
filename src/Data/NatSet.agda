{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Simple implementation of sets of ℕ.
--------------------------------------------------------------------------------

module Data.NatSet where

open import Data.Nat   as ℕ     using (ℕ; suc; zero)
open import Data.List  as List  using (List; _∷_; [])
open import Data.Maybe as Maybe using (Maybe; just; nothing)

open import Function

NatSet : Set
NatSet = List ℕ

insert : ℕ → NatSet → NatSet
insert x xs = List.para (f zero) (_∷ []) xs x
  where
  f : ℕ → ℕ → NatSet → (ℕ → NatSet) → (ℕ → NatSet)
  f k zero    xs g zero    = k ∷ xs
  f k zero    xs g (suc i) = k ∷ g i
  f k (suc x) xs g zero    = k ∷ x ∷ xs
  f k (suc x) xs g (suc i) = f (suc k) x xs g i

delete : ℕ → NatSet → NatSet
delete x [] = []
delete x (y ∷ ys) with ℕ.compare x y
delete x (y ∷ ys) | ℕ.less .x k = y ∷ ys
delete x (y ∷ ys) | ℕ.greater .y k = y ∷ delete k ys
delete x (y ∷ []) | ℕ.equal .x = []
delete x (y₁ ∷ y₂ ∷ ys) | ℕ.equal .x = suc x ℕ.+ y₂ ∷ ys

-- Returns the position of the element, if it's present.
member : ℕ → NatSet → Maybe ℕ
member x xs = List.foldr f (const (const nothing)) xs x 0
  where
  f : ℕ → (ℕ → ℕ → Maybe ℕ) → ℕ → ℕ → Maybe ℕ
  f zero    ys zero    k = just k
  f zero    ys (suc x) k = ys x (suc k)
  f (suc y) ys zero    _ = nothing
  f (suc y) ys (suc x) k = f y ys x k

fromList : List ℕ → NatSet
fromList = List.foldr insert []

toList : NatSet → List ℕ
toList = List.drop 1 ∘ List.map ℕ.pred ∘ List.scanl (λ x y → suc (y ℕ.+ x)) 0

private
  open import Relation.Binary.PropositionalEquality
  example₁ : fromList (4 ∷ 3 ∷ 1 ∷ 0 ∷ 2 ∷ []) ≡ (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
  example₁ = refl

  example₂ : member 3 (fromList (4 ∷ 3 ∷ 1 ∷ 0 ∷ 2 ∷ [])) ≡ just 3
  example₂ = refl

  example₃ : toList (fromList (4 ∷ 3 ∷ 1 ∷ 0 ∷ 2 ∷ [])) ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  example₃ = refl

  example₄ : delete 3 (fromList (4 ∷ 3 ∷ 1 ∷ 2 ∷ [])) ≡ fromList (4 ∷ 1 ∷ 2 ∷ [])
  example₄ = refl

  example₅ : delete 3 (fromList (4 ∷ 1 ∷ 2 ∷ [])) ≡ fromList (4 ∷ 1 ∷ 2 ∷ [])
  example₅ = refl
