------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of n-ary products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Recursive.Properties where

open import Level using (Level)
open import Data.Nat.Base hiding (_^_)
open import Data.Product
open import Data.Vec.Recursive
open import Data.Vec.Base using (Vec; _∷_)
open import Function.Inverse using (_↔_; inverse)
open import Relation.Binary.PropositionalEquality as P
open ≡-Reasoning

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Basic proofs

cons-head-tail-identity : ∀ n (as : A ^ suc n) → cons n (head n as) (tail n as) ≡ as
cons-head-tail-identity 0       as = P.refl
cons-head-tail-identity (suc n) as = P.refl

head-cons-identity : ∀ n a (as : A ^ n) → head n (cons n a as) ≡ a
head-cons-identity 0       a as = P.refl
head-cons-identity (suc n) a as = P.refl

tail-cons-identity : ∀ n a (as : A ^ n) → tail n (cons n a as) ≡ as
tail-cons-identity 0       a as = P.refl
tail-cons-identity (suc n) a as = P.refl

append-cons-commute : ∀ m n a (xs : A ^ m) ys →
  append (suc m) n (cons m a xs) ys ≡ cons (m + n) a (append m n xs ys)
append-cons-commute 0       n a xs ys = P.refl
append-cons-commute (suc m) n a xs ys = P.refl

append-splitAt-identity : ∀ m n (as : A ^ (m + n)) → uncurry (append m n) (splitAt m n as) ≡ as
append-splitAt-identity 0       n as = P.refl
append-splitAt-identity (suc m) n as = begin
  let x         = head (m + n) as in
  let (xs , ys) = splitAt m n (tail (m + n) as) in
  append (suc m) n (cons m (head (m + n) as) xs) ys
    ≡⟨ append-cons-commute m n x xs ys ⟩
  cons (m + n) x (append m n xs ys)
    ≡⟨ P.cong (cons (m + n) x) (append-splitAt-identity m n (tail (m + n) as)) ⟩
  cons (m + n) x (tail (m + n) as)
    ≡⟨ cons-head-tail-identity (m + n) as ⟩
  as
    ∎

------------------------------------------------------------------------
-- Conversion to and from Vec

fromVec∘toVec : ∀ n (xs : A ^ n) → fromVec (toVec n xs) ≡ xs
fromVec∘toVec 0       _  = P.refl
fromVec∘toVec (suc n) xs = begin
  cons n (head n xs) (fromVec (toVec n (tail n xs)))
    ≡⟨ P.cong (cons n (head n xs)) (fromVec∘toVec n (tail n xs)) ⟩
  cons n (head n xs) (tail n xs)
    ≡⟨ cons-head-tail-identity n xs ⟩
  xs ∎

toVec∘fromVec : ∀ {n} (xs : Vec A n) → toVec n (fromVec xs) ≡ xs
toVec∘fromVec             Vec.[]       = P.refl
toVec∘fromVec {n = suc n} (x Vec.∷ xs) = begin
  head n (cons n x (fromVec xs)) Vec.∷ toVec n (tail n (cons n x (fromVec xs)))
    ≡⟨ P.cong₂ (λ x xs → x Vec.∷ toVec n xs) hd-prf tl-prf ⟩
  x Vec.∷ toVec n (fromVec xs)
    ≡⟨ P.cong (x Vec.∷_) (toVec∘fromVec xs) ⟩
  x Vec.∷ xs
    ∎ where

  hd-prf = head-cons-identity _ x (fromVec xs)
  tl-prf = tail-cons-identity _ x (fromVec xs)

↔Vec : ∀ n → A ^ n ↔ Vec A n
↔Vec n = inverse (toVec n) fromVec (fromVec∘toVec n) toVec∘fromVec
