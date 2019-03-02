------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on strings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.String.Properties where

open import Data.String.Base

import Data.Char.Properties as Charₚ
import Data.List.Properties as Listₚ

open import Function
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Primitive properties

open import Agda.Builtin.String.Properties
  renaming ( primStringToListInjective to toList-injective)
  public

_≟_ : Decidable {A = String} _≡_
x ≟ y = map′ (toList-injective x y) (cong toList)
      $ Listₚ.≡-dec Charₚ._≟_ (toList x) (toList y)
