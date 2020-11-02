------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for sums
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Instances where

open import Data.Sum.Base
open import Data.Sum.Properties
open import Level
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.TypeClasses

private
  variable
    a b : Level
    A : Set a
    B : Set b

instance
  ⊎-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → {{IsDecEquivalence {A = B} _≡_}} → IsDecEquivalence {A = A ⊎ B} _≡_
  ⊎-≡-isDecEquivalence = isDecEquivalence (≡-dec _≟_ _≟_)
