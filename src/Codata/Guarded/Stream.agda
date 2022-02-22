------------------------------------------------------------------------
-- The Agda standard library
--
-- Infinite streams defined as coinductive records
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K --guardedness #-}

module Codata.Guarded.Stream where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty.Base as List⁺ using (List⁺; _∷_; _∷⁺_)
open import Data.Nat.Base hiding (_⊔_)
open import Data.Product as P using (Σ; proj₁; proj₂; _×_; _,_)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Function.Base using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Nullary
open import Relation.Unary

private
  variable
    a b c ℓ : Level
    A : Set a
    B : Set b
    C : Set c

record Stream (A : Set a) : Set a where
  coinductive
  constructor _∷_
  field
    head : A
    tail : Stream A

open Stream public

repeat : A → Stream A
head (repeat x) = x
tail (repeat x) = repeat x

_++_ : List A → Stream A → Stream A
[] ++ ys = ys
(x ∷ xs) ++ ys = record
  { head = x
  ; tail = xs ++ ys
  }

lookup : ℕ → Stream A → A
lookup zero xs = head xs
lookup (suc n) xs = lookup n (tail xs)

iterate : (A → A) → A → Stream A
head (iterate f x) = x
tail (iterate f x) = iterate f (f x)

unfold : (A → A × B) → A → Stream B
head (unfold next seed) = P.proj₂ (next seed)
tail (unfold next seed) = unfold next (P.proj₁ (next seed))

nats : Stream ℕ
nats = iterate suc zero

tabulate : (ℕ → A) → Stream A
head (tabulate f) = f zero
tail (tabulate f) = tabulate (f ∘ suc)

map : (A → B) → Stream A → Stream B
head (map f xs) = f (head xs)
tail (map f xs) = map f (tail xs)

ap : Stream (A → B) → Stream A → Stream B
head (ap fs xs) = head fs (head xs)
tail (ap fs xs) = ap (tail fs) (tail xs)

zipWith : (A → B → C) → Stream A → Stream B → Stream C
head (zipWith f xs ys) = f (head xs) (head ys)
tail (zipWith f xs ys) = zipWith f (tail xs) (tail ys)

scanl : (B → A → B) → B → Stream A → Stream B
head (scanl f b xs) = b
tail (scanl f b xs) = scanl f (f b (head xs)) (tail xs)

tails : Stream A → Stream (Stream A)
head (tails xs) = xs
tail (tails xs) = tails (tail xs)

splitAt : (n : ℕ) → Stream A → Vec A n × Stream A
splitAt 0 xs = [] , xs
splitAt (suc n) xs = P.map₁ (head xs ∷_) (splitAt n (tail xs))

take : (n : ℕ) → Stream A → Vec A n
take n xs = P.proj₁ (splitAt n xs)

drop : (n : ℕ) → Stream A → Stream A
drop n xs = P.proj₂ (splitAt n xs)

chunksOf : (n : ℕ) → Stream A → Stream (Vec A n)
head (chunksOf n xs) = take n xs
tail (chunksOf n xs) = chunksOf n (drop n xs)

interleave : Stream A → Stream A → Stream A
head (interleave xs ys) = head xs
tail (interleave xs ys) = interleave ys (tail xs)

evens : Stream A → Stream A
head (evens xs) = head xs
tail (evens xs) = evens (tail (tail xs))

odds : Stream A → Stream A
head (odds xs) = head (tail xs)
tail (odds xs) = odds (tail (tail xs))

_⁺++_ : List⁺ A → Stream A → Stream A
head (xs ⁺++ ys) = List⁺.head xs
tail (xs ⁺++ ys) = List⁺.tail xs ++ ys

interleave⁺ : List⁺ (Stream A) → Stream A
interleave⁺ {A = A} (xs ∷ xss) = go [] xs xss
  where
    --    ,- tails of the streams we have already dealt with
    --   |                 ,-- current focus
    --   v                 v          v-- future work
    go : List (Stream A) → Stream A → List (Stream A) → Stream A
    head (go rev xs yss)        = head xs
    tail (go rev xs [])         = interleave⁺ (List⁺.reverse (tail xs ∷ rev))
    tail (go rev xs (ys ∷ yss)) = go (tail xs ∷ rev) ys yss

cycle : List⁺ A → Stream A
cycle {A = A} (x ∷ xs) = cycleAux []
  module Cycle where
    cycleAux : List A → Stream A
    head (cycleAux []) = x
    tail (cycleAux []) = cycleAux xs
    head (cycleAux (x ∷ xs)) = x
    tail (cycleAux (x ∷ xs)) = cycleAux xs

cantor : Stream (Stream A) → Stream A
cantor ls = zig (head ls ∷ []) (tail ls)
  where
    zig : List⁺ (Stream A) → Stream (Stream A) → Stream A
    zag : List⁺ A → List⁺ (Stream A) → Stream (Stream A) → Stream A

    zig xss = zag (List⁺.map head xss) (List⁺.map tail xss)

    head (zag (x ∷ []) zs ls) = x
    tail (zag (x ∷ []) zs ls) = zig (head ls ∷⁺ zs) (tail ls)
    head (zag (x ∷ y ∷ xs) zs ls) = x
    tail (zag (x ∷ y ∷ xs) zs ls) = zag (y ∷ xs) zs ls

plane : {B : A → Set b} → Stream A → ((a : A) → Stream (B a)) → Stream (Σ A B)
plane as bs = cantor (map (λ a → map (a ,_) (bs a)) as)
