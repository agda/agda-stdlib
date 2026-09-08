------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings: builtin type and basic operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.String.Base where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Char.Base as Char using (Char)
open import Data.List.Base as List using (List; [_]; _∷_; [])
open import Data.List.NonEmpty.Base as NE using (List⁺)
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise)
open import Data.List.Relation.Binary.Lex.Core using (Lex-<; Lex-≤)
open import Data.Maybe.Base as Maybe using (Maybe)
open import Data.Nat.Base using (ℕ; _∸_; ⌊_/2⌋; ⌈_/2⌉; _≡ᵇ_)
open import Data.Product.Base using (proj₁; proj₂)
open import Function.Base using (_on_; _∘′_; _∘_)
open import Level using (Level; 0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary.Decidable.Core using (does; T?)

------------------------------------------------------------------------
-- From Agda.Builtin: type and renamed primitives

-- Note that we do not re-export primStringAppend because we want to
-- give it an infix definition and be able to assign it a level.

import Agda.Builtin.String as String

open String public using ( String )
  renaming
  ( primStringUncons   to uncons
  ; primStringToList   to toList
  ; primStringFromList to fromList
  ; primShowString     to show
  )

------------------------------------------------------------------------
-- Relations

-- Pointwise equality on Strings

infix 4 _≈_
_≈_ : Rel String 0ℓ
_≈_ = Pointwise _≡_ on toList

-- Lexicographic ordering on Strings

infix 4 _<_
_<_ : Rel String 0ℓ
_<_ = Lex-< _≡_ Char._<_ on toList

infix 4 _≤_
_≤_ : Rel String 0ℓ
_≤_ = Lex-≤ _≡_ Char._<_ on toList

------------------------------------------------------------------------
-- Operations

-- List-like operations

head : String → Maybe Char
head = Maybe.map proj₁ ∘′ uncons

tail : String → Maybe String
tail = Maybe.map proj₂ ∘′ uncons

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

unwords : List String → String
unwords = intersperse " "

unlines : List String → String
unlines = intersperse "\n"

between : String → String → String → String
between left right middle = left ++ middle ++ right

parens : String → String
parens = between "(" ")"

braces : String → String
braces = between "{" "}"

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
padLeft c n str =
  let l = n ∸ length str in
  if l ≡ᵇ 0 then str else replicate l c ++ str

padRight : Char → ℕ → String → String
padRight c n str =
  let l = n ∸ length str in
  if l ≡ᵇ 0 then str else str ++ replicate l c

padBoth : Char → Char → ℕ → String → String
padBoth cₗ cᵣ n str =
  let l = n ∸ length str in
  if l ≡ᵇ 0 then str else replicate ⌊ l /2⌋ cₗ ++ str ++ replicate ⌈ l /2⌉ cᵣ

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
-- Splitting strings

wordsBy : ∀ {p} {P : Pred Char p} → Decidable P → String → List String
wordsBy P? = List.map fromList ∘ List.wordsBy P? ∘ toList

wordsByᵇ : (Char → Bool) → String → List String
wordsByᵇ p = wordsBy (T? ∘ p)

words : String → List String
words = wordsByᵇ Char.isSpace

-- `words` ignores contiguous whitespace
_ : words " abc  b   " ≡ "abc" ∷ "b" ∷ []
_ = refl

linesBy : ∀ {p} {P : Pred Char p} → Decidable P → String → List String
linesBy P? = List.map fromList ∘ List.linesBy P? ∘ toList

linesByᵇ : (Char → Bool) → String → List String
linesByᵇ p = linesBy (T? ∘ p)

lines : String → List String
lines = linesByᵇ ('\n' Char.≈ᵇ_)

-- `lines` preserves empty lines
_ : lines "\nabc\n\nb\n\n\n" ≡ "" ∷ "abc" ∷ "" ∷ "b" ∷ "" ∷ "" ∷ "" ∷ []
_ = refl

-- `lines` does not add a trailing newline
_ : lines "\nabc\n\nb" ≡ "" ∷ "abc" ∷ "" ∷ "b" ∷ []
_ = refl

map : (Char → Char) → String → String
map f = fromList ∘ List.map f ∘ toList

_ : map Char.toUpper "abc" ≡ "ABC"
_ = refl
