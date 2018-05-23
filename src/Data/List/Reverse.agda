------------------------------------------------------------------------
-- The Agda standard library
--
-- Reverse view
------------------------------------------------------------------------

module Data.List.Reverse where

open import Data.List.Base as L hiding (reverse)
open import Data.List.Properties
open import Function
open import Relation.Binary.PropositionalEquality

-- If you want to traverse a list from the end, then you can use the
-- reverse view of it.

infixl 5 _∶_∶ʳ_

data Reverse {A : Set} : List A → Set where
  []     : Reverse []
  _∶_∶ʳ_ : ∀ xs (rs : Reverse xs) (x : A) → Reverse (xs ∷ʳ x)

module _ {A : Set} where

  reverse : (xs : List A) → Reverse (L.reverse xs)
  reverse []       = []
  reverse (x ∷ xs) = cast $ _ ∶ reverse xs ∶ʳ x where
    cast = subst Reverse (sym $ unfold-reverse x xs)

  reverseView : (xs : List A) → Reverse xs
  reverseView xs = cast $ reverse (L.reverse xs) where
    cast = subst Reverse (reverse-involutive xs)
