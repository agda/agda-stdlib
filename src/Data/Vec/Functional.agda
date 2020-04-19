------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors defined as functions from a finite set to a type.
------------------------------------------------------------------------

-- This implementation is designed for reasoning about fixed-size
-- vectors where ease of retrieval of elements is prioritised.

-- See `Data.Vec` for an alternative implementation using inductive
-- data-types, which is more suitable for reasoning about vectors that
-- will grow or shrink in size.

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional where

open import Data.Fin.Base using (Fin; zero; suc; splitAt; punchIn)
open import Data.List.Base as L using (List)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec.Base as V using (Vec)
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

------------------------------------------------------------------------
-- Definition

Vector : Set a → ℕ → Set a
Vector A n = Fin n → A

------------------------------------------------------------------------
-- Conversion

toVec : ∀ {n} → Vector A n → Vec A n
toVec = V.tabulate

fromVec : ∀ {n} → Vec A n → Vector A n
fromVec = V.lookup

toList : ∀ {n} → Vector A n → List A
toList = L.tabulate

fromList : ∀ (xs : List A) → Vector A (L.length xs)
fromList = L.lookup

------------------------------------------------------------------------
-- Construction and deconstruction

[] : Vector A zero
[] ()

_∷_ : ∀ {n} → A → Vector A n → Vector A (suc n)
(x ∷ xs) zero    = x
(x ∷ xs) (suc i) = xs i

head : ∀ {n} → Vector A (suc n) → A
head xs = xs zero

tail : ∀ {n} → Vector A (suc n) → Vector A n
tail xs = xs ∘ suc

uncons : ∀ {n} → Vector A (suc n) → A × Vector A n
uncons xs = head xs , tail xs

replicate : ∀ {n} → A → Vector A n
replicate = const

remove : ∀ {n} → Fin (suc n) → Vector A (suc n) → Vector A n
remove i t = t ∘ punchIn i

------------------------------------------------------------------------
-- Transformations

map : (A → B) → ∀ {n} → Vector A n → Vector B n
map f xs = f ∘ xs

_++_ : ∀ {m n} → Vector A m → Vector A n → Vector A (m + n)
_++_ {m = m} xs ys i = [ xs , ys ] (splitAt m i)

foldr : (A → B → B) → B → ∀ {n} → Vector A n → B
foldr f z {n = zero}  xs = z
foldr f z {n = suc n} xs = f (head xs) (foldr f z (tail xs))

foldl : (B → A → B) → B → ∀ {n} → Vector A n → B
foldl f z {n = zero}  xs = z
foldl f z {n = suc n} xs = foldl f (f z (head xs)) (tail xs)

rearrange : ∀ {m n} → (Fin m → Fin n) → Vector A n → Vector A m
rearrange r xs = xs ∘ r

_⊛_ : ∀ {n} → Vector (A → B) n → Vector A n → Vector B n
_⊛_ = _ˢ_

zipWith : (A → B → C) → ∀ {n} → Vector A n → Vector B n → Vector C n
zipWith f xs ys i = f (xs i) (ys i)

zip : ∀ {n} → Vector A n → Vector B n → Vector (A × B) n
zip = zipWith _,_
