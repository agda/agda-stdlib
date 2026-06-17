------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of n-ary products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Recursive.Properties where

open import Level using (Level)
open import Data.Nat.Base hiding (_^_)
open import Data.Product.Base
open import Data.Vec.Recursive
open import Data.Vec.Base using (Vec; _∷_)
open import Function.Bundles using (_↔_; mk↔ₛ′)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong₂)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open ≡-Reasoning

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Basic proofs

cons-head-tail-identity : ∀ n (as : A ^ suc n) → cons n (head n as) (tail n as) ≡ as
cons-head-tail-identity 0       as = refl
cons-head-tail-identity (suc n) as = refl

head-cons-identity : ∀ n a (as : A ^ n) → head n (cons n a as) ≡ a
head-cons-identity 0       a as = refl
head-cons-identity (suc n) a as = refl

tail-cons-identity : ∀ n a (as : A ^ n) → tail n (cons n a as) ≡ as
tail-cons-identity 0       a as = refl
tail-cons-identity (suc n) a as = refl

append-cons : ∀ m n a (xs : A ^ m) ys →
  append (suc m) n (cons m a xs) ys ≡ cons (m + n) a (append m n xs ys)
append-cons 0       n a xs ys = refl
append-cons (suc m) n a xs ys = refl

append-splitAt-identity : ∀ m n (as : A ^ (m + n)) → uncurry (append m n) (splitAt m n as) ≡ as
append-splitAt-identity 0       n as = refl
append-splitAt-identity (suc m) n as = begin
  let x         = head (m + n) as in
  let (xs , ys) = splitAt m n (tail (m + n) as) in
  append (suc m) n (cons m (head (m + n) as) xs) ys
    ≡⟨ append-cons m n x xs ys ⟩
  cons (m + n) x (append m n xs ys)
    ≡⟨ cong (cons (m + n) x) (append-splitAt-identity m n (tail (m + n) as)) ⟩
  cons (m + n) x (tail (m + n) as)
    ≡⟨ cons-head-tail-identity (m + n) as ⟩
  as
    ∎

------------------------------------------------------------------------
-- Conversion to and from Vec

fromVec∘toVec : ∀ n (xs : A ^ n) → fromVec (toVec n xs) ≡ xs
fromVec∘toVec 0       _  = refl
fromVec∘toVec (suc n) xs = begin
  cons n (head n xs) (fromVec (toVec n (tail n xs)))
    ≡⟨ cong (cons n (head n xs)) (fromVec∘toVec n (tail n xs)) ⟩
  cons n (head n xs) (tail n xs)
    ≡⟨ cons-head-tail-identity n xs ⟩
  xs ∎

toVec∘fromVec : ∀ {n} (xs : Vec A n) → toVec n (fromVec xs) ≡ xs
toVec∘fromVec             Vec.[]       = refl
toVec∘fromVec {n = suc n} (x Vec.∷ xs) = begin
  head n (cons n x (fromVec xs)) Vec.∷ toVec n (tail n (cons n x (fromVec xs)))
    ≡⟨ cong₂ (λ x xs → x Vec.∷ toVec n xs) hd-prf tl-prf ⟩
  x Vec.∷ toVec n (fromVec xs)
    ≡⟨ cong (x Vec.∷_) (toVec∘fromVec xs) ⟩
  x Vec.∷ xs
    ∎ where

  hd-prf = head-cons-identity _ x (fromVec xs)
  tl-prf = tail-cons-identity _ x (fromVec xs)

↔Vec : ∀ n → A ^ n ↔ Vec A n
↔Vec n = mk↔ₛ′ (toVec n) fromVec toVec∘fromVec (fromVec∘toVec n)

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

append-cons-commute = append-cons
{-# WARNING_ON_USAGE append-cons-commute
"Warning: append-cons-commute was deprecated in v2.0.
Please use append-cons instead."
#-}
