------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings: builtin type and basic operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.String.Base where

open import Level using (zero)
open import Data.Nat.Base as Nat using (ℕ)
open import Data.List.Base as List using (List)
open import Data.List.NonEmpty as NE using (List⁺)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
open import Data.List.Relation.Binary.Lex.Strict using (Lex-<)
open import Data.Char.Base as Char using (Char)
open import Function
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality

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

fromList⁺ : List⁺ Char → String
fromList⁺ = fromList ∘ NE.toList

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
