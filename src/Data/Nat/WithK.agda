------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural number types and operations requiring the axiom K.
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Nat.WithK where

open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality.WithK

≤″-erase : ∀ {m n} → m ≤″ n → m ≤″ n
≤″-erase (less-than-or-equal eq) = less-than-or-equal (≡-erase eq)

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.18

erase = ≤″-erase
{-# WARNING_ON_USAGE erase
"Warning: erase was deprecated in v0.18.
Please use ≤″-erase instead."
#-}
