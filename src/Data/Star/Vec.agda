------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors defined in terms of the reflexive-transitive closure, Star
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Star.Vec where

open import Data.Star.Nat using (ℕ; zero; suc; 1#; _+_; length)
open import Data.Star.Fin using (Fin)
open import Data.Star.Decoration using (All; ↦; _◅◅◅_; decoration)
open import Data.Star.Pointer as Pointer using (result)
open import Data.Star.List using (List)
open import Level using (Level)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (ε; _◅_; gmap)
open import Function.Base using (const; case_of_)
open import Data.Unit.Base using (tt)

private
  variable
    a : Level
    A : Set a

-- The vector type. Vectors are natural numbers decorated with extra
-- information (i.e. elements).

Vec : Set a → ℕ → Set a
Vec A = All (λ _ → A)

-- Nil and cons.

[] : Vec A zero
[] = ε

infixr 5 _∷_

_∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
x ∷ xs = ↦ x ◅ xs

-- Projections.

head : ∀ {n} → Vec A (1# + n) → A
head (↦ x ◅ _) = x

tail : ∀ {n} → Vec A (1# + n) → Vec A n
tail (↦ _ ◅ xs) = xs

-- Append.

infixr 5 _++_

_++_ : ∀ {m n} → Vec A m → Vec A n → Vec A (m + n)
_++_ = _◅◅◅_

-- Safe lookup.

lookup : ∀ {n} → Vec A n → Fin n → A
lookup xs i with result _ x ← Pointer.lookup xs i = x

------------------------------------------------------------------------
-- Conversions

fromList : (xs : List A) → Vec A (length xs)
fromList ε        = []
fromList (x ◅ xs) = x ∷ fromList xs

toList : ∀ {n} → Vec A n → List A
toList = gmap (const tt) decoration
