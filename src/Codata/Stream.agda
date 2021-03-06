------------------------------------------------------------------------
-- The Agda standard library
--
-- The Stream type and some operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Codata.Stream where

open import Size
open import Codata.Thunk as Thunk using (Thunk; force)

open import Data.Nat.Base
open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Product as P hiding (map)
open import Function.Base
open import Level using (Level)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    i : Size

------------------------------------------------------------------------
-- Type

data Stream (A : Set a) (i : Size) : Set a where
  _∷_ : A → Thunk (Stream A) i → Stream A i

------------------------------------------------------------------------
-- Creating streams

repeat : A → Stream A i
repeat a = a ∷ λ where .force → repeat a

infixr 5 _++_ _⁺++_
_++_ : List A → Stream A i → Stream A i
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ λ where .force → xs ++ ys

unfold : (A → A × B) → A → Stream B i
unfold next seed =
  let (seed′ , b) = next seed in
  b ∷ λ where .force → unfold next seed′

iterate : (A → A) → A → Stream A ∞
iterate f = unfold < f , id >

nats : Stream ℕ ∞
nats = iterate suc zero

------------------------------------------------------------------------
-- Looking at streams

head : Stream A i → A
head (x ∷ xs) = x

tail : ∀ {i} {j : Size< i} → Stream A i → Stream A j
tail (x ∷ xs) = xs .force

lookup : ℕ → Stream A ∞ → A
lookup zero    xs = head xs
lookup (suc k) xs = lookup k (tail xs)

------------------------------------------------------------------------
-- Transforming streams

map : (A → B) → Stream A i → Stream B i
map f (x ∷ xs) = f x ∷ λ where .force → map f (xs .force)

ap : Stream (A → B) i → Stream A i → Stream B i
ap (f ∷ fs) (x ∷ xs) = f x ∷ λ where .force → ap (fs .force) (xs .force)

scanl : (B → A → B) → B → Stream A i → Stream B i
scanl c n (x ∷ xs) = n ∷ λ where .force → scanl c (c n x) (xs .force)

zipWith : (A → B → C) → Stream A i → Stream B i → Stream C i
zipWith f (a ∷ as) (b ∷ bs) = f a b ∷ λ where .force → zipWith f (as .force) (bs .force)

------------------------------------------------------------------------
-- List⁺-related functions

_⁺++_ : List⁺ A → Thunk (Stream A) i → Stream A i
(x ∷ xs) ⁺++ ys = x ∷ λ where .force → xs ++ ys .force

cycle : List⁺ A → Stream A i
cycle xs = xs ⁺++ λ where .force → cycle xs

concat : Stream (List⁺ A) i → Stream A i
concat (xs ∷ xss) = xs ⁺++ λ where .force → concat (xss .force)

------------------------------------------------------------------------
-- Chunking

splitAt : (n : ℕ) → Stream A ∞ → Vec A n × Stream A ∞
splitAt zero    xs       = [] , xs
splitAt (suc n) (x ∷ xs) = P.map₁ (x ∷_) (splitAt n (xs .force))

take : (n : ℕ) → Stream A ∞ → Vec A n
take n xs = proj₁ (splitAt n xs)

drop : ℕ → Stream A ∞ → Stream A ∞
drop n xs = proj₂ (splitAt n xs)

chunksOf : (n : ℕ) → Stream A ∞ → Stream (Vec A n) ∞
chunksOf n = chunksOfAcc n id module ChunksOf where

  chunksOfAcc : ∀ {i} k (acc : Vec A k → Vec A n) →
                Stream A ∞ → Stream (Vec A n) i
  chunksOfAcc zero    acc xs       = acc [] ∷ λ where .force → chunksOfAcc n id xs
  chunksOfAcc (suc k) acc (x ∷ xs) = chunksOfAcc k (acc ∘ (x ∷_)) (xs .force)

------------------------------------------------------------------------
-- Interleaving streams

-- The most basic of interleaving strategies is to take two streams and
-- alternate between emitting values from one and the other.
interleave : Stream A i → Thunk (Stream A) i → Stream A i
interleave (x ∷ xs) ys = x ∷ λ where .force → interleave (ys .force) xs
