------------------------------------------------------------------------
-- The Agda standard library
--
-- Strings
------------------------------------------------------------------------

module Data.String.Base where

open import Data.Nat.Base as Nat using (ℕ)
open import Data.List.Base as List using (_∷_; []; List)
open import Data.Bool.Base using (Bool)
open import Data.Char.Core using (Char)
open import Function
open import Relation.Binary.Core using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

------------------------------------------------------------------------
-- From Agda.Builtin

open import Agda.Builtin.String public
  using ( String
        ; primStringAppend
        ; primStringToList
        ; primStringFromList
        ; primStringEquality
        ; primShowString )

------------------------------------------------------------------------
-- Operations

-- Conversion functions

toList : String → List Char
toList = primStringToList

fromList : List Char → String
fromList = primStringFromList

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

------------------------------------------------------------------------
-- Properties

toList∘fromList : ∀ s → toList (fromList s) ≡ s
toList∘fromList s = trustMe

fromList∘toList : ∀ s → fromList (toList s) ≡ s
fromList∘toList s = trustMe
