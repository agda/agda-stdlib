------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists defined in terms of the reflexive-transitive closure, Star
------------------------------------------------------------------------

module Data.Star.List where

open import Data.Star.Nat
open import Data.Unit
open import Relation.Binary.Simple
open import Relation.Binary.Closure.ReflexiveTransitive

-- Lists.

List : Set → Set
List a = Star (Const a) tt tt

-- Nil and cons.

[] : ∀ {a} → List a
[] = ε

infixr 5 _∷_

_∷_ : ∀ {a} → a → List a → List a
_∷_ = _◅_

-- The sum of the elements in a list containing natural numbers.

sum : List ℕ → ℕ
sum = fold (Star Always) _+_ zero
