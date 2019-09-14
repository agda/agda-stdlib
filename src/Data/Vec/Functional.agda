------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors defined via index notation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional where

open import Data.Fin using (Fin; zero; suc; splitAt)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
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
map f xs = f ∘ xs

rearrange : ∀ {m n} → (Fin m → Fin n) → (Vector A n → Vector A m)
rearrange r xs = xs ∘ r

[] : Vector A zero
[] ()

_∷_ : ∀ {n} → A → Vector A n → Vector A (suc n)
(x ∷ xs) zero = x
(x ∷ xs) (suc i) = xs i

head : ∀ {n} → Vector A (suc n) → A
head xs = xs zero

tail : ∀ {n} → Vector A (suc n) → Vector A n
tail xs = xs ∘ suc

uncons : ∀ {n} → Vector A (suc n) → A × Vector A n
uncons xs = head xs , tail xs

_++_ : ∀ {m n} → Vector A m → Vector A n → Vector A (m + n)
_++_ {m = m} xs ys i = [ xs , ys ] (splitAt m i)

foldr : (A → B → B) → B → ∀ {n} → Vector A n → B
foldr f z {n = zero} xs = z
foldr f z {n = suc n} xs = f (head xs) (foldr f z (tail xs))

foldl : (B → A → B) → B → ∀ {n} → Vector A n → B
foldl f z {n = zero} xs = z
foldl f z {n = suc n} xs = foldl f (f z (head xs)) (tail xs)

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
