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
open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality.Core
import Relation.Binary.PropositionalEquality as PropEq

------------------------------------------------------------------------
-- Primitive properties

open import Agda.Builtin.String.Properties
  renaming ( primStringToListInjective to toList-injective)
  public

------------------------------------------------------------------------
-- Decidable equality

_≟_ : Decidable {A = String} _≡_
x ≟ y = map′ (toList-injective x y) (cong toList)
      $ Listₚ.≡-dec Charₚ._≟_ (toList x) (toList y)

decSetoid : DecSetoid _ _
decSetoid = PropEq.decSetoid _≟_
