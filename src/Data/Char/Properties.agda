------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on characters
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Char.Properties where

open import Data.Char.Base

import Data.Nat.Properties as ℕₚ

open import Function
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Primitive properties

open import Agda.Builtin.Char.Properties
  renaming ( primCharToNatInjective to toNat-injective)
  public

_≟_ : Decidable {A = Char} _≡_
x ≟ y = map′ (toNat-injective x y) (cong toNat)
      $ toNat x ℕₚ.≟ toNat y
