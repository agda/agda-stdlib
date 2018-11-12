------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors defined in terms of the reflexive-transitive closure, Star
------------------------------------------------------------------------

module Data.Star.Vec where

open import Data.Star.Nat
open import Data.Star.Fin using (Fin)
open import Data.Star.Decoration
open import Data.Star.Pointer as Pointer hiding (lookup)
open import Data.Star.List using (List)
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Function
open import Data.Unit

-- The vector type. Vectors are natural numbers decorated with extra
-- information (i.e. elements).

Vec : Set → ℕ → Set
Vec A = All (λ _ → A)

-- Nil and cons.

[] : ∀ {A} → Vec A zero
[] = ε

infixr 5 _∷_

_∷_ : ∀ {A n} → A → Vec A n → Vec A (suc n)
x ∷ xs = ↦ x ◅ xs

-- Projections.

head : ∀ {A n} → Vec A (1# + n) → A
head (↦ x ◅ _) = x

tail : ∀ {A n} → Vec A (1# + n) → Vec A n
tail (↦ _ ◅ xs) = xs

-- Append.

infixr 5 _++_

_++_ : ∀ {A m n} → Vec A m → Vec A n → Vec A (m + n)
_++_ = _◅◅◅_

-- Safe lookup.

lookup : ∀ {A n} → Fin n → Vec A n → A
lookup i xs with Pointer.lookup i xs
... | result _ x = x

------------------------------------------------------------------------
-- Conversions

fromList : ∀ {A} → (xs : List A) → Vec A (length xs)
fromList ε        = []
fromList (x ◅ xs) = x ∷ fromList xs

toList : ∀ {A n} → Vec A n → List A
toList = gmap (const tt) decoration
