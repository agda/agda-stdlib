------------------------------------------------------------------------
-- The Agda standard library
--
-- DiffList: basic types and operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.DifferenceList.Base where

open import Data.List.Base as List using (List)
open import Data.Nat.Base using (ℕ)
open import Function using (_∘′_; id)
open import Level using (Level)

private
  variable
    a b : Level
    A : Set a
    B : Set b


------------------------------------------------------------------------
-- Type definition

DiffList : Set a → Set a
DiffList A = List A → List A

------------------------------------------------------------------------
-- Building difference lists

infixr 5 _∷_ _++_

[] : DiffList A
[] = id

[_] : A → DiffList A
[ x ] = x List.∷_

_++_ : DiffList A → DiffList A → DiffList A
_++_ = _∘′_

_∷_ : A → DiffList A → DiffList A
x ∷ xs = [ x ] ++ xs

infixl 6 _∷ʳ_
_∷ʳ_ : DiffList A → A → DiffList A
xs ∷ʳ x = xs ++ [ x ]

------------------------------------------------------------------------
-- Conversion back and forth with List

toList : DiffList A → List A
toList xs = xs List.[]

-- fromList xs is linear in the length of xs.

fromList : List A → DiffList A
fromList = List._++_

-- Careful: viaList reifies the difference list to apply
-- the list-base transformation.

viaList : (List A → List B) → (DiffList A → DiffList B)
viaList f = fromList ∘′ f ∘′ toList

------------------------------------------------------------------------
-- Transforming difference lists

-- It is OK to use viaList here, since map is linear in the length of
-- the list anyway.

map : (A → B) → DiffList A → DiffList B
map = viaList ∘′ List.map

-- concat is linear in the length of the outer list.

concat : DiffList (DiffList A) → DiffList A
concat = List.foldr _++_ [] ∘′ toList



------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 3.0
lift : DiffList A → DiffList A → DiffList A
lift = _++_
{-# WARNING_ON_USAGE lift
"Warning: lift was deprecated in v3.0.
Please use _++_ instead."
#-}

take : ℕ → DiffList A → DiffList A
take n = List.take n ++_
{-# WARNING_ON_USAGE take
"Warning: take was deprecated in v3.0 as it is not the
lawful counterpart of List.take"
#-}

drop : ℕ → DiffList A → DiffList A
drop n = List.drop n ++_
{-# WARNING_ON_USAGE drop
"Warning: drop was deprecated in v3.0 as it is not the
lawful counterpart of List.drop"
#-}
