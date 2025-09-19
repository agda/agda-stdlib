------------------------------------------------------------------------
-- The Agda standard library
--
-- Structures for order-theoretic filters
------------------------------------------------------------------------
-- As per our discussion, we should add the definition of a filter to
-- agda-stdlib.

-- ## Background

-- First, some background. Let (P, ≤) be a preorder (or more generally, I
-- guess just a relation `R : P → P → Set`). A *filter* of size κ in P consists of
-- a predicate `F : P → Set κ` that satisfies the following conditions:

-- - `F` is upwards closed: if x ≤ y and F(x), then F(y)
-- - `F` is downwards directed: there exists some x with F(x), and for
-- - every x, y : P with F(x) and F(y), there exists some z : P with
--   F(z) × z ≤ x × z ≤ y

-- Some useful facts:

-- - If P is a meet semilattice, then conditions 1 and 2 jointly imply that
--   F(⊤), and conditions 1 and 3 mean that F(x) × F(y) → F(x ∧ y), where ∧
--   is the meet.
-- - Alternatively, if P is a meet semilattice, then a κ-small filter is
--   equivalent to a meet semilattice homomorphism P → Type κ, where the
--   unit type is the top element, and meets are given by products of
--   types.

-- ## Programming

-- There does need to be some thought as to organization. We should go with
-- the definition I listed first as our primary definition, as it is the
-- most general. The useful facts would be nice to prove as theorems.

-- Moreover, I think we should place the definition either in it's own file
-- `Relation.Binary.Filter`, or inside of a folder like
-- `Relation.Binary.Diagram.Filter`; not sure here. Theorems would be
-- somewhere in Relation.Binary.Lattice.Filter or something.

-- We might want to factor out the "downward directed" and "upwards closed" bits into their own
-- definitions? Could also place all of this in `Relation.Binary.Subset` or
-- something, as they are all definitions regarding subsets of binary
-- relations? Note that there are also "downwards closed" and "upwards
-- directed" sets, so be careful with names!

-- PS: for bonus points, you could also add *ideals* in a preorder: these
-- are the duals of filters; IE: downwards-closed, upwards directed.

-- Hope that makes sense,
-- Reed :)
{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Filter where

open import Relation.Binary.Core using (Rel)
open import Data.Product.Base using (∃-syntax; _×_; _,_)
open import Level
open import Relation.Binary.Structures using (IsPreorder)
open import Relation.Binary.Definitions using (_Respects_)
open import Function.Base using (flip)

private
  variable
    a κ ℓ₁ ℓ₂ : Level
    A : Set a

UpwardClosure : (A → Set ℓ₁) → Rel A ℓ₂ → Set _
UpwardClosure F _≤_ = F Respects _≤_

DownwardDirectdness : (A → Set ℓ₁) → Rel A ℓ₂ → Set _
DownwardDirectdness {A = A} F _≤_ = (∃[ x ] F x) × (∀ x y → (F x) × (F y) → ∃[ z ] (F z × z ≤ x × z ≤ y))

DownwardClosure : (A → Set ℓ₁) → Rel A ℓ₂ → Set _
DownwardClosure {A = A} F _≤_ = UpwardClosure F (flip _≤_)

UpwardDirectdness : (A → Set ℓ₁) → Rel A ℓ₂ → Set _
UpwardDirectdness {A = A} F _≤_ = DownwardDirectdness F (flip _≤_)

record IsFilter {a κ ℓ} {A : Set κ} (F : A → Set κ) (_≤_ : Rel A ℓ) : Set (a ⊔ κ ⊔ ℓ) where
  field
    upClosed     : UpwardClosure F _≤_
    downDirected : DownwardDirectdness F _≤_

record IsIdeal {a κ ℓ} {A : Set κ} (F : A → Set κ) (_≤_ : Rel A ℓ) : Set (a ⊔ κ ⊔ ℓ) where
  field
    downClosed : DownwardClosure F _≤_
    upDirected : UpwardDirectdness F _≤_


