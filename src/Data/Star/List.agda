------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists defined in terms of the reflexive-transitive closure, Star
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Star.List where

open import Data.Star.Nat using (ℕ; _+_; zero)
open import Data.Unit.Base using (tt)
open import Relation.Binary.Construct.Always using (Always)
open import Relation.Binary.Construct.Constant using (Const)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_; fold)

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
