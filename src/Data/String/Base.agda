------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings: builtin type and basic operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.String.Base where

open import Level using (zero)
open import Data.Bool using (true; false)
open import Data.Nat.Base as ℕ using (ℕ; _∸_; ⌊_/2⌋; ⌈_/2⌉)
import Data.Nat.Properties as ℕₚ
open import Data.List.Base as List using (List; [_])
open import Data.List.NonEmpty as NE using (List⁺)
open import Data.List.Extrema ℕₚ.≤-totalOrder
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Binary.Lex.Strict using (Lex-<)
open import Data.Vec.Base as Vec using (Vec)
open import Data.Char.Base as Char using (Char)
import Data.Char.Properties as Char using (_≟_)
open import Function
open import Relation.Binary using (Rel)
open import Relation.Nullary using (does)

open import Data.List.Membership.DecPropositional Char._≟_

------------------------------------------------------------------------
-- From Agda.Builtin: type and renamed primitives

-- Note that we do not re-export primStringAppend because we want to
-- give it an infix definition and be able to assign it a level.

import Agda.Builtin.String as String

open String public using ( String )
  renaming
  ( primStringToList   to toList
  ; primStringFromList to fromList
  ; primShowString     to show
  )

------------------------------------------------------------------------
-- Relations

-- Pointwise equality on Strings

infix 4 _≈_
_≈_ : Rel String zero
_≈_ = Pointwise Char._≈_ on toList

-- Lexicographic ordering on Strings

infix 4 _<_
_<_ : Rel String zero
_<_ = Lex-< Char._≈_ Char._<_ on toList

------------------------------------------------------------------------
-- Operations

-- Additional conversion functions

fromChar : Char → String
fromChar = fromList ∘′ [_]

fromList⁺ : List⁺ Char → String
fromList⁺ = fromList ∘′ NE.toList

-- List-like functions

infixr 5 _++_
_++_ : String → String → String
_++_ = String.primStringAppend

length : String → ℕ
length = List.length ∘ toList

replicate : ℕ → Char → String
replicate n = fromList ∘ List.replicate n

concat : List String → String
concat = List.foldr _++_ ""

intersperse : String → List String → String
intersperse sep = concat ∘′ (List.intersperse sep)

-- String-specific functions

unlines : List String → String
unlines = intersperse "\n"

unwords : List String → String
unwords = intersperse " "

parens : String → String
parens s = "(" ++ s ++ ")"

-- enclose string with parens if it contains a space character
parensIfSpace : String → String
parensIfSpace s with does (' ' ∈? toList s)
... | true  = parens s
... | false = s

braces : String → String
braces s = "{" ++ s ++ "}"

-- append that also introduces spaces, if necessary
infixr 5 _<+>_
_<+>_ : String → String → String
"" <+> b = b
a <+> "" = a
a <+> b = a ++ " " ++ b

------------------------------------------------------------------------
-- Padding

-- Each one of the padding functions should verify the following
-- invariant:
--   If length str ≤ n then length (padLeft c n str) ≡ n
--   and otherwise padLeft c n str ≡ str.

-- Appending an empty string is expensive (append for Haskell's
-- Text creates a fresh Text value in which both contents are
-- copied) so we precompute `n ∸ length str` and check whether
-- it is equal to 0.

padLeft : Char → ℕ → String → String
padLeft c n str with n ∸ length str
... | 0 = str
... | l = replicate l c ++ str

padRight : Char → ℕ → String → String
padRight c n str with n ∸ length str
... | 0 = str
... | l = str ++ replicate l c

padBoth : Char → Char → ℕ → String → String
padBoth cₗ cᵣ n str with n ∸ length str
... | 0 = str
... | l = replicate ⌊ l /2⌋ cₗ ++ str ++ replicate ⌈ l /2⌉ cᵣ

------------------------------------------------------------------------
-- Alignment

-- We can align a String left, center or right in a column of a given
-- width by padding it with whitespace.

data Alignment : Set where
  Left Center Right : Alignment

fromAlignment : Alignment → ℕ → String → String
fromAlignment Left   = padRight ' '
fromAlignment Center = padBoth ' ' ' '
fromAlignment Right  = padLeft ' '

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
