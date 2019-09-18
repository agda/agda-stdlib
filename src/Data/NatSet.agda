{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Simple implementation of sets of ℕ.
--------------------------------------------------------------------------------

module Data.NatSet where

open import Data.Nat   as ℕ     using (ℕ; suc; zero)
open import Data.List  as List  using (List; _∷_; [])
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Bool  as Bool  using (Bool)

open import Function

open import Relation.Binary.PropositionalEquality

NatSet : Set
NatSet = List ℕ

insert : ℕ → NatSet → NatSet
insert x xs = List.para f (_∷ []) xs x
  where
  f : ℕ → NatSet → (ℕ → NatSet) → ℕ → NatSet
  f y ys c x with ℕ.compare x y
  ... | ℕ.less x k    = x ∷ k ∷ ys
  ... | ℕ.equal x     = x ∷ ys
  ... | ℕ.greater y k = y ∷ c k

delete : ℕ → NatSet → NatSet
delete x xs = List.para f (const []) xs x
  where
  f : ℕ → NatSet → (ℕ → NatSet) → ℕ → NatSet
  f y ys c x with ℕ.compare x y
  f y ys c x | ℕ.less .x k = y ∷ ys
  f y ys c x | ℕ.greater .y k = y ∷ c k
  f y [] c x | ℕ.equal .x = []
  f y₁ (y₂ ∷ ys) c x | ℕ.equal .x = suc x ℕ.+ y₂ ∷ ys

-- Returns the position of the element, if it's present.
lookup : ℕ → NatSet → Maybe ℕ
lookup x xs = List.foldr f (const (const nothing)) xs x 0
  where
  f : ℕ → (ℕ → ℕ → Maybe ℕ) → ℕ → ℕ → Maybe ℕ
  f y ys x i with ℕ.compare x y
  ... | ℕ.less .x k = nothing
  ... | ℕ.equal .y = just i
  ... | ℕ.greater .y k = ys k (suc i)

member : ℕ → NatSet → Bool
member x = Maybe.is-just ∘ lookup x

fromList : List ℕ → NatSet
fromList = List.foldr insert []

toList : NatSet → List ℕ
toList = List.drop 1 ∘ List.map ℕ.pred ∘ List.scanl (λ x y → suc (y ℕ.+ x)) 0

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
