------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists with fast append
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.DifferenceList where

open import Level using (Level)
open import Data.List.Base as List using (List)
open import Function
open import Data.Nat.Base

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Type definition and list function lifting

DiffList : Set a → Set a
DiffList A = List A → List A

lift : (List A → List A) → (DiffList A → DiffList A)
lift f xs = λ k → f (xs k)

------------------------------------------------------------------------
-- Building difference lists

infixr 5 _∷_ _++_

[] : DiffList A
[] = λ k → k

_∷_ : A → DiffList A → DiffList A
_∷_ x = lift (x List.∷_)

[_] : A → DiffList A
[ x ] = x ∷ []

_++_ : DiffList A → DiffList A → DiffList A
xs ++ ys = λ k → xs (ys k)

infixl 6 _∷ʳ_
_∷ʳ_ : DiffList A → A → DiffList A
xs ∷ʳ x = λ k → xs (x List.∷ k)

------------------------------------------------------------------------
-- Conversion back and forth with List

toList : DiffList A → List A
toList xs = xs List.[]

-- fromList xs is linear in the length of xs.

fromList : List A → DiffList A
fromList xs = λ k → xs ⟨ List._++_ ⟩ k

------------------------------------------------------------------------
-- Transforming difference lists

-- It is OK to use List._++_ here, since map is linear in the length of
-- the list anyway.

map : (A → B) → DiffList A → DiffList B
map f xs = λ k → List.map f (toList xs) ⟨ List._++_ ⟩ k

-- concat is linear in the length of the outer list.

concat : DiffList (DiffList A) → DiffList A
concat xs = concat' (toList xs)
  where
  concat' : List (DiffList A) → DiffList A
  concat' = List.foldr _++_ []

take : ℕ → DiffList A → DiffList A
take n = lift (List.take n)

drop : ℕ → DiffList A → DiffList A
drop n = lift (List.drop n)
