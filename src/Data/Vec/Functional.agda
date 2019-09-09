------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors defined via index notation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Vec as V using (Vec)
open import Function
open import Level using (Level)

infixr 5 _∷_ _++_
infixl 4 _⊛_

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

Vector : Set a → ℕ → Set a
Vector A n = Fin n → A

map : (A → B) → ∀ {n} → (Vector A n → Vector B n)
map f v = f ∘ v

rearrange : ∀ {m n} → (Fin m → Fin n) → (Vector A n → Vector A m)
rearrange r v = v ∘ r

[] : Vector A zero
[] ()

_∷_ : ∀ {n} → A → Vector A n → Vector A (suc n)
(x ∷ v) zero = x
(x ∷ v) (suc i) = v i

head : ∀ {n} → Vector A (suc n) → A
head v = v zero

tail : ∀ {n} → Vector A (suc n) → Vector A n
tail v = v ∘ suc

uncons : ∀ {n} → Vector A (suc n) → A × Vector A n
uncons v = head v , tail v

_++_ : ∀ {m n} → Vector A m → Vector A n → Vector A (m + n)
_++_ {m = zero} u v i = v i
_++_ {m = suc m} u v zero = u zero
_++_ {m = suc m} u v (suc i) = (tail u ++ v) i

foldr : (A → B → B) → B → ∀ {n} → Vector A n → B
foldr f z {n = zero} v = z
foldr f z {n = suc n} v = f (head v) (foldr f z (tail v))

foldl : (B → A → B) → B → ∀ {n} → Vector A n → B
foldl f z {n = zero} v = z
foldl f z {n = suc n} v = foldl f (f z (head v)) (tail v)

toVec : ∀ {n} → Vector A n → Vec A n
toVec = V.tabulate

fromVec : ∀ {n} → Vec A n → Vector A n
fromVec = V.lookup

replicate : ∀ {n} → A → Vector A n
replicate = const

_⊛_ : ∀ {n} → Vector (A → B) n → Vector A n → Vector B n
_⊛_ = _ˢ_

zipWith : (A → B → C) → ∀ {n} → Vector A n → Vector B n → Vector C n
zipWith f xs ys = replicate f ⊛ xs ⊛ ys

zip : ∀ {n} → Vector A n → Vector B n → Vector (A × B) n
zip = zipWith _,_
