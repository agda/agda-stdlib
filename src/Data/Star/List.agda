------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists defined in terms of the reflexive-transitive closure, Star
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Star.List where

open import Data.Star.Nat
open import Data.Unit
open import Relation.Binary.Construct.Always using (Always)
open import Relation.Binary.Construct.Constant using (Const)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive

-- Lists.

List : ∀ {a} → Set a → Set a
List A = Star (Const A) tt tt

-- Nil and cons.

[] : ∀ {a} {A : Set a} → List A
[] = ε

infixr 5 _∷_

_∷_ : ∀ {a} {A : Set a} → A → List A → List A
_∷_ = _◅_

-- The sum of the elements in a list containing natural numbers.

sum : List ℕ → ℕ
sum = fold (Star Always) _+_ zero
