------------------------------------------------------------------------
-- The Agda standard library
--
-- Subsets of finite sets
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Subset where

open import Algebra
import Algebra.Properties.BooleanAlgebra as BoolAlgProp
import Algebra.Properties.BooleanAlgebra.Expression as BAExpr
open import Data.Bool using (not; _∧_; _∨_; _≟_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; foldr; foldl)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (∃; _×_)
open import Data.Vec hiding (foldr; foldl)
import Data.Vec.Relation.Binary.Pointwise.Extensional as Pointwise
open import Relation.Nullary

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Definitions

-- Partitions a finite set into two parts, the inside and the outside.
-- Note that it would be great to shorten these to `in` and `out` but
-- `in` is a keyword (e.g. let ... in ...)

-- Sides.

open import Data.Bool.Base public
  using () renaming (Bool to Side; true to inside; false to outside)

-- Subset

Subset : ℕ → Set
Subset = Vec Side

------------------------------------------------------------------------
-- Special subsets

-- The empty subset
⊥ : Subset n
⊥ = replicate outside

-- The full subset
⊤ : Subset n
⊤ = replicate inside

-- A singleton subset, containing just the given element.
⁅_⁆ : Fin n → Subset n
⁅ zero  ⁆ = inside  ∷ ⊥
⁅ suc i ⁆ = outside ∷ ⁅ i ⁆

------------------------------------------------------------------------
-- Membership and subset predicates

infix 4 _∈_ _∉_ _⊆_ _⊈_ _⊂_ _⊄_

_∈_ : Fin n → Subset n → Set
x ∈ p = p [ x ]= inside

_∉_ : Fin n → Subset n → Set
x ∉ p = ¬ (x ∈ p)

_⊆_ : Subset n → Subset n → Set
p ⊆ q = ∀ {x} → x ∈ p → x ∈ q

_⊈_ : Subset n → Subset n → Set
p ⊈ q = ¬ (p ⊆ q)

_⊂_ : Subset n → Subset n → Set
p ⊂ q = p ⊆ q × ∃ (λ x → x ∈ q × x ∉ p)

_⊄_ : Subset n → Subset n → Set
p ⊄ q = ¬ (p ⊂ q)

------------------------------------------------------------------------
-- Set operations

infixr 7 _∩_
infixr 6 _∪_
infixl 5 _─_ _-_

-- Complement
∁ : Op₁ (Subset n)
∁ p = map not p

-- Intersection
_∩_ : Op₂ (Subset n)
p ∩ q = zipWith _∧_ p q

-- Union
_∪_ : Op₂ (Subset n)
p ∪ q = zipWith _∨_ p q

-- Difference
_─_ : Op₂ (Subset n)
p ─ q = zipWith diff p q
  where
  diff : Side → Side → Side
  diff x inside  = outside
  diff x outside = x

-- N-ary union
⋃ : List (Subset n) → Subset n
⋃ = foldr _∪_ ⊥

-- N-ary intersection
⋂ : List (Subset n) → Subset n
⋂ = foldr _∩_ ⊤

-- Element removal
_-_ : Subset n → Fin n → Subset n
p - x = p ─ ⁅ x ⁆

-- Size
∣_∣ : Subset n → ℕ
∣ p ∣ = count (_≟ inside) p

------------------------------------------------------------------------
-- Properties

Nonempty : ∀ (p : Subset n) → Set
Nonempty p = ∃ λ f → f ∈ p

Empty : ∀ (p : Subset n) → Set
Empty p = ¬ Nonempty p

Lift : ∀ {ℓ} → (Fin n → Set ℓ) → (Subset n → Set ℓ)
Lift P p = ∀ {x} → x ∈ p → P x
