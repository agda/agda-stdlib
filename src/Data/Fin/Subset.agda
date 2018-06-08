------------------------------------------------------------------------
-- The Agda standard library
--
-- Subsets of finite sets
------------------------------------------------------------------------

module Data.Fin.Subset where

open import Algebra
open import Algebra.FunctionProperties using (Op₁; Op₂)
import Algebra.Properties.BooleanAlgebra as BoolAlgProp
import Algebra.Properties.BooleanAlgebra.Expression as BAExpr
open import Data.Bool using (not; _∧_; _∨_; _≟_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; foldr; foldl)
open import Data.Nat using (ℕ)
open import Data.Product using (∃)
open import Data.Vec hiding (_∈_; foldr; foldl)
import Data.Vec.Relation.Pointwise.Extensional as Pointwise
open import Relation.Nullary

------------------------------------------------------------------------
-- Definitions

-- Sides.

open import Data.Bool.Base public
  using () renaming (Bool to Side; true to inside; false to outside)

-- Partitions a finite set into two parts, the inside and the outside.

Subset : ℕ → Set
Subset = Vec Side

------------------------------------------------------------------------
-- Special subsets

-- The empty subset
⊥ : ∀ {n} → Subset n
⊥ = replicate outside

-- The full subset
⊤ : ∀ {n} → Subset n
⊤ = replicate inside

-- A singleton subset, containing just the given element.
⁅_⁆ : ∀ {n} → Fin n → Subset n
⁅ zero  ⁆ = inside  ∷ ⊥
⁅ suc i ⁆ = outside ∷ ⁅ i ⁆

------------------------------------------------------------------------
-- Membership and subset predicates

infix 4 _∈_ _∉_ _⊆_ _⊈_

_∈_ : ∀ {n} → Fin n → Subset n → Set
x ∈ p = p [ x ]= inside

_∉_ : ∀ {n} → Fin n → Subset n → Set
x ∉ p = ¬ (x ∈ p)

_⊆_ : ∀ {n} → Subset n → Subset n → Set
p ⊆ q = ∀ {x} → x ∈ p → x ∈ q

_⊈_ : ∀ {n} → Subset n → Subset n → Set
p ⊈ q = ¬ (p ⊆ q)

------------------------------------------------------------------------
-- Set operations

infixr 7 _∩_
infixr 6 _∪_

-- Complement
∁ : ∀ {n} → Op₁ (Subset n)
∁ p = map not p

-- Union
_∩_ : ∀ {n} → Op₂ (Subset n)
p ∩ q = zipWith _∧_ p q

-- Intersection
_∪_ : ∀ {n} → Op₂ (Subset n)
p ∪ q = zipWith _∨_ p q

-- N-ary union
⋃ : ∀ {n} → List (Subset n) → Subset n
⋃ = foldr _∪_ ⊥

-- N-ary intersection
⋂ : ∀ {n} → List (Subset n) → Subset n
⋂ = foldr _∩_ ⊤

-- Size
∣_∣ : ∀ {n} → Subset n → ℕ
∣ p ∣ = count (_≟ inside) p

------------------------------------------------------------------------
-- Properties

Nonempty : ∀ {n} (p : Subset n) → Set
Nonempty p = ∃ λ f → f ∈ p

Empty : ∀ {n} (p : Subset n) → Set
Empty p = ¬ Nonempty p

-- Point-wise lifting of properties.
Lift : ∀ {n ℓ} → (Fin n → Set ℓ) → (Subset n → Set ℓ)
Lift P p = ∀ {x} → x ∈ p → P x
