------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Instances where

open import Data.Product.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_)
open import Relation.Binary.Structures
  using (IsDecEquivalence)
open import Relation.Binary.TypeClasses

instance
  ≡-isDecEquivalence-Σ = λ {a} {b} {A} {B} {{≡-isDecEquivalence-A}} {{≡-isDecEquivalence-B : ∀ {a} → IsDecEquivalence (_≡_ {A = B a})}} → isDecEquivalence (≡-dec {a} {A = A} {b} {B = B} (_≟_ {{≡-isDecEquivalence-A}}) (_≟_ {{≡-isDecEquivalence-B}}))
