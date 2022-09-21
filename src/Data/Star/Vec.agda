------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors defined in terms of the reflexive-transitive closure, Star
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Star.Vec where

open import Data.Star.Nat
open import Data.Star.Fin using (Fin)
open import Data.Star.Decoration
open import Data.Star.Pointer as Pointer hiding (lookup)
open import Data.Star.List using (List)
open import Level using (Level)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Function.Base
open import Data.Unit

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
lookup xs i with Pointer.lookup xs i
... | result _ x = x

------------------------------------------------------------------------
-- Conversions

fromList : (xs : List A) → Vec A (length xs)
fromList ε        = []
fromList (x ◅ xs) = x ∷ fromList xs

toList : ∀ {n} → Vec A n → List A
toList = gmap (const tt) decoration
