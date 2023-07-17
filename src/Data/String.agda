------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.String where

open import Data.Bool using (true; false; T?)
open import Function.Base
open import Data.Nat.Base as ℕ using (ℕ; _∸_; ⌊_/2⌋; ⌈_/2⌉)
import Data.Nat.Properties as ℕₚ
open import Data.List.Base as List using (List; _∷_; []; [_])
open import Data.List.NonEmpty as NE using (List⁺)
open import Data.List.Extrema ℕₚ.≤-totalOrder
open import Data.Vec.Base as Vec using (Vec)
open import Data.Char.Base as Char using (Char)

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
rectangleˡ c = rectangle (Vec.replicate $ padLeft c)

rectangleʳ : ∀ {n} → Char → Vec String n → Vec String n
rectangleʳ c = rectangle (Vec.replicate $ padRight c)


rectangleᶜ : ∀ {n} → Char → Char → Vec String n → Vec String n
rectangleᶜ cₗ cᵣ = rectangle (Vec.replicate $ padBoth cₗ cᵣ)
