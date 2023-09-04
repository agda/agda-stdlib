------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-empty lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.NonEmpty where

open import Level using (Level)
open import Data.List.Base as List using (List)

------------------------------------------------------------------------
-- Re-export basic type and operations

open import Data.List.NonEmpty.Base public


------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

private
  variable
    a : Level
    A : Set a

-- Version 1.4

infixl 5 _∷ʳ'_

_∷ʳ'_ : (xs : List A) (x : A) → SnocView (xs ∷ʳ x)
_∷ʳ'_ = SnocView._∷ʳ′_
{-# WARNING_ON_USAGE _∷ʳ'_
"Warning: _∷ʳ'_ (ending in an apostrophe) was deprecated in v1.4.
Please use _∷ʳ′_ (ending in a prime) instead."
#-}
