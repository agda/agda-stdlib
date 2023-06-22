------------------------------------------------------------------------
-- The Agda standard library
--
-- Infinite streams defined as coinductive records
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe --guardedness #-}

module Codata.Guarded.Stream where

open import Level hiding (suc)
open import Data.Nat.Base
open import Function.Base
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Product hiding (map)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.List.NonEmpty.Base as List⁺ using (List⁺; _∷_)
open import Algebra.Core
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Type

infixr 5 _∷_

record Stream (A : Set a) : Set a where
  coinductive
  constructor _∷_
  field
    head : A
    tail : Stream A

open Stream public

------------------------------------------------------------------------
-- Creating streams

tabulate : (ℕ → A) → Stream A
tabulate f .head = f 0
tabulate f .tail = tabulate (f ∘′ suc)

repeat : A → Stream A
repeat = tabulate ∘′ const

infixr 5 _++_
_++_ : List A → Stream A → Stream A
[] ++ s = s
(x ∷ xs) ++ s = x ∷ xs ++ s

unfold : (A → A × B) → A → Stream B
unfold next seed .head = next seed .proj₂
unfold next seed .tail = unfold next (next seed .proj₁)

iterate : (A → A) → A → Stream A
iterate f = unfold < f , id >

nats : Stream ℕ
nats = tabulate id

------------------------------------------------------------------------
-- Lookup

lookup : Stream A → ℕ → A
lookup xs zero    = head xs
lookup xs (suc n) = lookup (tail xs) n

infix 4 _[_]

_[_] : Stream A → ℕ → A
_[_] = lookup

------------------------------------------------------------------------
-- Transforming streams

map : (A → B) → Stream A → Stream B
map f s .head = f (s .head)
map f s .tail = map f (s .tail)

ap : Stream (A → B) → Stream A → Stream B
ap fs xs .head = fs .head (xs .head)
ap fs xs .tail = ap (fs .tail) (xs .tail)

scanl : (B → A → B) → B → Stream A → Stream B
scanl c n s .head = n
scanl c n s .tail = scanl c (c n (s .head)) (s .tail)

zipWith : (A → B → C) → Stream A → Stream B → Stream C
zipWith f s t .head = f (s .head) (t .head)
zipWith f s t .tail = zipWith f (s .tail) (t .tail)

transpose : List (Stream A) → Stream (List A)
transpose [] = repeat []
transpose (s ∷ ss) = zipWith _∷_ s (transpose ss)

tails : Stream A → Stream (Stream A)
tails s .head = s
tails s .tail = tails (s .tail)

evens : Stream A → Stream A
evens s .head = s .head
evens s .tail = evens (s .tail .tail)

odds : Stream A → Stream A
odds s = evens (s .tail)

------------------------------------------------------------------------
-- List⁺-related functions

infixr 5 _⁺++_
_⁺++_ : List⁺ A → Stream A → Stream A
(x ∷ xs) ⁺++ ys = x ∷ xs ++ ys

concat : Stream (List⁺ A) → Stream A
concat {A = A} = ++-concat []
  module Concat where
    ++-concat : List A → Stream (List⁺ A) → Stream A
    ++-concat [] s .head = s .head .List⁺.head
    ++-concat [] s .tail = ++-concat (s .head .List⁺.tail) (s .tail)
    ++-concat (x ∷ xs) s .head = x
    ++-concat (x ∷ xs) s .tail = ++-concat xs s

cycle : List⁺ A → Stream A
cycle = concat ∘′ repeat

transpose⁺ : List⁺ (Stream A) → Stream (List⁺ A)
transpose⁺ (s ∷ ss) = zipWith _∷_ s (transpose ss)

------------------------------------------------------------------------
-- Chunking

splitAt : ∀ n → Stream A → Vec A n × Stream A
splitAt zero s = [] ,′ s
splitAt (suc n) s = map₁ (s .head ∷_) (splitAt n (s .tail))

take : ∀ n → Stream A → Vec A n
take = proj₁ ∘₂ splitAt

drop : ℕ → Stream A → Stream A
drop = proj₂ ∘₂ splitAt

chunksOf : ∀ n → Stream A → Stream (Vec A n)
chunksOf n s .head = take n s
chunksOf n s .tail = chunksOf n (drop n s)

------------------------------------------------------------------------
-- Interleaving streams

-- Interleaving two streams
interleave : Op₂ (Stream A)
interleave xs ys .head = xs .head
interleave xs ys .tail = interleave ys (xs .tail)

-- Interleaving multiple streams
interleave⁺ : List⁺ (Stream A) → Stream A
interleave⁺ = concat ∘′ transpose⁺

-- Interleaving a stream of streams using Cantor's zig zag function
-- (inverse of Cantor's pairing function)
cantor : Stream (Stream A) → Stream A
cantor s .head = s .head .head
cantor s .tail = cantor (zipWith _∷_ (s .head .tail) (s .tail))

-- A version of `bind` using the zig zag function that reaches any
-- point of the plane in a finite amout of time
plane : {B : A → Set b} → Stream A → (∀ a → Stream (B a)) → Stream (Σ A B)
plane xs fs = cantor (map (λ x → map (x ,_) (fs x)) xs)

-- Here is the beginning of the path we are following:
_ : take 21 (plane nats (const nats))
  ≡ (0 , 0)
  ∷ (0 , 1) ∷ (1 , 0)
  ∷ (0 , 2) ∷ (1 , 1) ∷ (2 , 0)
  ∷ (0 , 3) ∷ (1 , 2) ∷ (2 , 1) ∷ (3 , 0)
  ∷ (0 , 4) ∷ (1 , 3) ∷ (2 , 2) ∷ (3 , 1) ∷ (4 , 0)
  ∷ (0 , 5) ∷ (1 , 4) ∷ (2 , 3) ∷ (3 , 2) ∷ (4 , 1) ∷ (5 , 0)
  ∷ []
_ = refl
