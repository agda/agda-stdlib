------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for These
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.These.Instances where

open import Data.These.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.TypeClasses

instance
  ≡-isDecEquivalence-These = λ {a} {b} {A} {B} {{≡-isDecEquivalence-A}} {{≡-isDecEquivalence-B}} → isDecEquivalence (≡-dec {a} {b} {A = A} {B = B} (_≟_ {{≡-isDecEquivalence-A}}) (_≟_ {{≡-isDecEquivalence-B}}))
