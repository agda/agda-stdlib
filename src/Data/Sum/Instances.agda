------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for sums
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Instances where

open import Data.Sum.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.TypeClasses

instance
  ≡-isDecEquivalence-⊎ = λ {a} {b} {A} {B} {{≡-isDecEquivalence-A}} {{≡-isDecEquivalence-B}} → isDecEquivalence (≡-dec {a} {A = A} {b} {B = B} (_≟_ {{≡-isDecEquivalence-A}}) (_≟_ {{≡-isDecEquivalence-B}}))
