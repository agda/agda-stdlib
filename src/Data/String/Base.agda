------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings
------------------------------------------------------------------------

module Data.String.Base where

open import Data.Nat.Base as Nat using (ℕ)
open import Data.List.Base as List using (List)
open import Data.List.NonEmpty as NE using (List⁺)
open import Agda.Builtin.Char using (Char)
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- From Agda.Builtin

open import Agda.Builtin.String public
  using
  ( String
  ; primStringAppend
  ; primStringToList
  ; primStringFromList
  ; primStringEquality
  ; primShowString
  )

------------------------------------------------------------------------
-- Operations

-- Conversion functions

toList : String → List Char
toList = primStringToList

fromList : List Char → String
fromList = primStringFromList

fromList⁺ : List⁺ Char → String
fromList⁺ = fromList ∘ NE.toList

-- List-like functions

infixr 5 _++_
_++_ : String → String → String
_++_ = primStringAppend

length : String → ℕ
length = List.length ∘ toList

replicate : ℕ → Char → String
replicate n = fromList ∘ List.replicate n

concat : List String → String
concat = List.foldr _++_ ""

-- String-specific functions

show : String → String
show = primShowString

unlines : List String → String
unlines = concat ∘ List.intersperse "\n"
