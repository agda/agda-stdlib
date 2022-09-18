------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-empty lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.NonEmpty where

open import Level using (Level)
open import Effect.Monad
open import Data.Bool.Base using (Bool; false; true; not; T)
open import Data.Bool.Properties
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe ; nothing; just)
open import Data.Nat.Base as ℕ
open import Data.Product as Prod using (∃; _×_; proj₁; proj₂; _,_; -,_)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.These.Base as These using (These; this; that; these)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Function.Base
open import Function.Bundles using () renaming (module Equivalence to Eq)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable using (isYes)

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
