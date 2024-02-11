------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors with fast append
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.DifferenceVec where

open import Data.DifferenceNat
open import Data.Vec.Base as Vec using (Vec)
open import Function.Base using (_⟨_⟩_)
import Data.Nat.Base as ℕ

infixr 5 _∷_ _++_

DiffVec : ∀ {ℓ} → Set ℓ → Diffℕ → Set ℓ
DiffVec A m = ∀ {n} → Vec A n → Vec A (m n)

[] : ∀ {a} {A : Set a} → DiffVec A 0#
[] = λ k → k

_∷_ : ∀ {a} {A : Set a} {n} → A → DiffVec A n → DiffVec A (suc n)
x ∷ xs = λ k → Vec._∷_ x (xs k)

[_] : ∀ {a} {A : Set a} → A → DiffVec A 1#
[ x ] = x ∷ []

_++_ : ∀ {a} {A : Set a} {m n} →
       DiffVec A m → DiffVec A n → DiffVec A (m + n)
xs ++ ys = λ k → xs (ys k)

toVec : ∀ {a} {A : Set a} {n} → DiffVec A n → Vec A (toℕ n)
toVec xs = xs Vec.[]

-- fromVec xs is linear in the length of xs.

fromVec : ∀ {a} {A : Set a} {n} → Vec A n → DiffVec A (fromℕ n)
fromVec xs = λ k → xs ⟨ Vec._++_ ⟩ k

head : ∀ {a} {A : Set a} {n} → DiffVec A (suc n) → A
head xs = Vec.head (toVec xs)

tail : ∀ {a} {A : Set a} {n} → DiffVec A (suc n) → DiffVec A n
tail xs = λ k → Vec.tail (xs k)

take : ∀ {a} {A : Set a} m {n} →
       DiffVec A (fromℕ m + n) → DiffVec A (fromℕ m)
take ℕ.zero    xs = []
take (ℕ.suc m) xs = head xs ∷ take m (tail xs)

drop : ∀ {a} {A : Set a} m {n} →
       DiffVec A (fromℕ m + n) → DiffVec A n
drop ℕ.zero    xs = xs
drop (ℕ.suc m) xs = drop m (tail xs)
