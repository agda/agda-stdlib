------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.String where

open import Data.Bool using (true; false; T?)
open import Data.Char as Char using (Char)
open import Function.Base
open import Data.Nat.Base as ℕ using (ℕ; _∸_; ⌊_/2⌋; ⌈_/2⌉)
import Data.Nat.Properties as ℕₚ
open import Data.List.Base as List using (List; _∷_; []; [_])
open import Data.List.NonEmpty as NE using (List⁺)
open import Data.List.Extrema ℕₚ.≤-totalOrder
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Binary.Lex.Strict using (Lex-<; Lex-≤)
open import Data.Vec.Base as Vec using (Vec)
open import Data.Char.Base as Char using (Char)
import Data.Char.Properties as Char using (_≟_)
open import Function
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)
open import Relation.Unary using (Pred; Decidable)

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
parensIfSpace s with does (' ' ∈? toList s)
... | true  = parens s
... | false = s

------------------------------------------------------------------------
-- Splitting strings

wordsBy : ∀ {p} {P : Pred Char p} → Decidable P → String → List String
wordsBy P? = List.map fromList ∘ List.wordsBy P? ∘ toList

words : String → List String
words = wordsBy (T? ∘ Char.isSpace)

-- `words` ignores contiguous whitespace
_ : words " abc  b   " ≡ "abc" ∷ "b" ∷ []
_ = refl

linesBy : ∀ {p} {P : Pred Char p} → Decidable P → String → List String
linesBy P? = List.map fromList ∘ List.linesBy P? ∘ toList

lines : String → List String
lines = linesBy ('\n' Char.≟_)

-- `lines` preserves empty lines
_ : lines "\nabc\n\nb\n\n\n" ≡ "" ∷ "abc" ∷ "" ∷ "b" ∷ "" ∷ "" ∷ []
_ = refl

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
