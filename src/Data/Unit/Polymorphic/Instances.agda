------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for the polymorphic unit type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Unit.Polymorphic.Instances where

open import Data.Unit.Polymorphic.Base
open import Data.Unit.Polymorphic.Properties
open import Level
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.TypeClasses
  using (IsDecEquivalence; IsDecTotalOrder)

private
  variable
    a : Level

instance
  ⊤-≡-isDecEquivalence : IsDecEquivalence {A = ⊤ {a}} _≡_
  ⊤-≡-isDecEquivalence = isDecEquivalence _≟_

  ⊤-≤-isDecTotalOrder : IsDecTotalOrder {A = ⊤ {a}} _≡_ _≡_
  ⊤-≤-isDecTotalOrder = ≡-isDecTotalOrder _
