------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Instances where

open import Data.Product
  using (Σ)
open import Data.Product.Properties
open import Level
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_)
open import Relation.Binary.Structures
  using (IsDecEquivalence)
open import Relation.Binary.TypeClasses

private
  variable
    a b : Level
    A : Set a

instance
  Σ-≡-isDecEquivalence : ∀ {B : A → Set b} {{_ : IsDecEquivalence {A = A} _≡_}} {{_ : ∀ {a} → IsDecEquivalence {A = B a} _≡_}} → IsDecEquivalence {A = Σ A B} _≡_
  Σ-≡-isDecEquivalence = isDecEquivalence (≡-dec _≟_ _≟_)
