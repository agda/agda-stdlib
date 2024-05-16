------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic auxiliary definitions for magma-like structures
------------------------------------------------------------------------

-- You're unlikely to want to use this module directly. Instead you
-- probably want to be importing the appropriate module from
-- `Algebra.Properties.(Magma/Semigroup/...).Divisibility`

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles.Raw using (RawMagma)
open import Data.Product.Base using (_×_; ∃)
open import Level using (_⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary.Negation.Core using (¬_)

module Algebra.Definitions.RawMagma
  {a ℓ} (M : RawMagma a ℓ)
  where

open RawMagma M renaming (Carrier to A)

------------------------------------------------------------------------
-- Divisibility

infix 5 _∣ˡ_ _∤ˡ_ _∣ʳ_ _∤ʳ_ _∣_ _∤_ _∣∣_ _∤∤_

-- Divisibility from the left.
--
-- This and, the definition of right divisibility below, are defined as
-- records rather than in terms of the base product type in order to
-- make the use of pattern synonyms more ergonomic (see #2216 for
-- further details). The record field names are not designed to be
-- used explicitly and indeed aren't re-exported publicly by
-- `Algebra.X.Properties.Divisibility` modules.

record _∣ˡ_ (x y : A) : Set (a ⊔ ℓ) where
  constructor _,_
  field
    quotient : A
    equality : x ∙ quotient ≈ y

_∤ˡ_ : Rel A (a ⊔ ℓ)
x ∤ˡ y = ¬ x ∣ˡ y

-- Divisibility from the right

record _∣ʳ_ (x y : A) : Set (a ⊔ ℓ) where
  constructor _,_
  field
    quotient : A
    equality : quotient ∙ x ≈ y

_∤ʳ_ : Rel A (a ⊔ ℓ)
x ∤ʳ y = ¬ x ∣ʳ y

-- General divisibility

-- The relations _∣ˡ_ and _∣ʳ_ are only equivalent when _∙_ is
-- commutative. When that is not the case we take `_∣ʳ_` to be the
-- primary one.

_∣_ : Rel A (a ⊔ ℓ)
_∣_ = _∣ʳ_

_∤_ : Rel A (a ⊔ ℓ)
x ∤ y = ¬ x ∣ y

------------------------------------------------------------------------
-- Mutual divisibility.

-- In a  monoid, this is an equivalence relation extending _≈_.
-- When in a cancellative monoid,  elements related by _∣∣_ are called
-- associated, and `x ∣∣ y` means that `x` and `y` differ by some
-- invertible factor.

-- Example: for ℕ  this is equivalent to x ≡ y,
--          for ℤ  this is equivalent to (x ≡ y or x ≡ - y).

_∣∣_ : Rel A (a ⊔ ℓ)
x ∣∣ y = x ∣ y × y ∣ x

_∤∤_ : Rel A (a ⊔ ℓ)
x ∤∤ y = ¬ x ∣∣ y
