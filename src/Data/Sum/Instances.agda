------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for sums
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Sum.Instances where

open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (≡-dec)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.TypeClasses using (IsDecEquivalence; _≟_)

private
  variable
    a b : Level
    A : Set a
    B : Set b

instance
  ⊎-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → {{IsDecEquivalence {A = B} _≡_}} → IsDecEquivalence {A = A ⊎ B} _≡_
  ⊎-≡-isDecEquivalence = isDecEquivalence (≡-dec _≟_ _≟_)
