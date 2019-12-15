------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings: builtin type and basic operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.String.Base where

open import Level using (zero)
open import Data.Nat.Base as Nat using (ℕ; ⌊_/2⌋; ⌈_/2⌉)
import Data.Nat.Properties as ℕₚ
open import Data.List.Base as List using (List; [_])
open import Data.List.NonEmpty as NE using (List⁺)
open import Data.List.Extrema ℕₚ.≤-totalOrder
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Binary.Lex.Strict using (Lex-<)
open import Data.Vec.Base as Vec using (Vec)
open import Data.Char.Base as Char using (Char)
open import Function
open import Relation.Binary using (Rel)

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

-- String-specific functions

unlines : List String → String
unlines = concat ∘ List.intersperse "\n"

padLeft : Char → ℕ → String → String
padLeft c n str = replicate (n Nat.∸ length str) c ++ str

padRight : Char → ℕ → String → String
padRight c n str with n Nat.∸ length str
... | 0 = str
... | l = str ++ replicate l c

padBoth : Char → Char → ℕ → String → String
padBoth cₗ cᵣ n str with n Nat.∸ length str
... | 0 = str
... | l = replicate ⌊ l /2⌋ cₗ ++ str ++ replicate ⌈ l /2⌉ cᵣ

rectangle : ∀ {n} → (ℕ → String → String) →
            Vec String n → Vec String n
rectangle pad cells = Vec.map (pad width) cells where

  sizes = List.map length (Vec.toList cells)
  width = max 0 sizes

rectangleˡ : ∀ {n} → Char → Vec String n → Vec String n
rectangleˡ c = rectangle (padLeft c)

rectangleʳ : ∀ {n} → Char → Vec String n → Vec String n
rectangleʳ c = rectangle (padRight c)

rectangleᶜ : ∀ {n} → Char → Char → Vec String n → Vec String n
rectangleᶜ cₗ cᵣ = rectangle (padBoth cₗ cᵣ)
