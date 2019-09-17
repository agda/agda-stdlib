{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Simple implementation of sets of ℕ.
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Table where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.List as List using (List; _∷_; [])
open import Function

Table : Set
Table = List ℕ

para : ∀ {a b} {A : Set a} {B : Set b} → (A → List A → B → B) → B → List A → B
para f b [] = b
para f b (x ∷ xs) = f x xs (para f b xs)

insert : ℕ → Table → Table
insert x xs = para (go zero) (_∷ []) xs x
  where
  go : ℕ → ℕ → Table → (ℕ → Table) → ℕ → Table
  go k zero    xs g zero    = k ∷ xs
  go k zero    xs g (suc i) = k ∷ g i
  go k (suc x) xs g zero    = k ∷ x ∷ xs
  go k (suc x) xs g (suc i) = go (suc k) x xs g i

open import Data.Maybe as Maybe using (Maybe; just; nothing)

member : ℕ → Table → Maybe ℕ
member x xs = List.foldr go (const (const nothing)) xs x 0
  where
  go : ℕ → (ℕ → ℕ → Maybe ℕ) → ℕ → ℕ → Maybe ℕ
  go zero    ys zero    k = just k
  go zero    ys (suc x) k = ys x (suc k)
  go (suc y) ys zero    _ = nothing
  go (suc y) ys (suc x) k = go y ys x k

fromList : List ℕ → Table
fromList = List.foldr insert []

toList : Table → List ℕ
toList = tail′ ∘ List.map ℕ.pred ∘ List.scanl (λ x y → suc (y ℕ.+ x)) 0
  where
  tail′ : List ℕ → List ℕ
  tail′ [] = []
  tail′ (_ ∷ xs) = xs

private
  open import Relation.Binary.PropositionalEquality
  example₁ : fromList (4 ∷ 3 ∷ 1 ∷ 0 ∷ 2 ∷ []) ≡ (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
  example₁ = refl

  example₂ : member 3 (fromList (4 ∷ 3 ∷ 1 ∷ 0 ∷ 2 ∷ [])) ≡ just 3
  example₂ = refl

  example₃ : toList (fromList (4 ∷ 3 ∷ 1 ∷ 0 ∷ 2 ∷ [])) ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  example₃ = refl
