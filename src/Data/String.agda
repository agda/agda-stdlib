------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.String where

open import Data.Bool.Base using (if_then_else_)
open import Data.Char.Base as Char using (Char)
open import Function.Base using (_∘_; _$_)
open import Data.Nat.Base as ℕ using (ℕ)
import Data.Nat.Properties as ℕ
open import Data.List.Base as List using (List)
open import Data.List.Extrema ℕ.≤-totalOrder
open import Data.Vec.Base as Vec using (Vec)
open import Data.Char.Base as Char using (Char)
import Data.Char.Properties as Char using (_≟_)
open import Relation.Nullary.Decidable.Core using (does)

open import Data.List.Membership.DecPropositional Char._≟_


------------------------------------------------------------------------
-- Re-export contents of base, and decidability of equality

open import Data.String.Base public
open import Data.String.Properties using (_≈?_; _≟_; _<?_; _==_) public

------------------------------------------------------------------------
-- Conversion functions

toVec : (s : String) → Vec Char (length s)
toVec s = Vec.fromList (toList s)

fromVec : ∀ {n} → Vec Char n → String
fromVec = fromList ∘ Vec.toList


-- enclose string with parens if it contains a space character
parensIfSpace : String → String
parensIfSpace s = if does (' ' ∈? toList s) then parens s else s


------------------------------------------------------------------------
-- Rectangle

-- Build a rectangular column by:
-- Given a vector of cells and a padding function for each one
-- Compute the max of the widths, and pad the strings accordingly.

rectangle : ∀ {n} → Vec (ℕ → String → String) n →
            Vec String n → Vec String n
rectangle pads cells = Vec.zipWith (λ p c → p width c) pads cells where

  sizes = List.map length (Vec.toList cells)
  width = max 0 sizes

-- Special cases for left, center, and right alignment

rectangleˡ : ∀ {n} → Char → Vec String n → Vec String n
rectangleˡ c = rectangle (Vec.replicate _ $ padLeft c)

rectangleʳ : ∀ {n} → Char → Vec String n → Vec String n
rectangleʳ c = rectangle (Vec.replicate _ $ padRight c)

rectangleᶜ : ∀ {n} → Char → Char → Vec String n → Vec String n
rectangleᶜ cₗ cᵣ = rectangle (Vec.replicate _ $ padBoth cₗ cᵣ)
