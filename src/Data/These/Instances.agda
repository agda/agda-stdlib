------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for These
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.These.Instances where

open import Data.These.Base
open import Data.These.Properties
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
  ≡-isDecEquivalence-These : {{IsDecEquivalence {A = A} _≡_}} → {{IsDecEquivalence {A = B} _≡_}} → IsDecEquivalence {A = These A B} _≡_
  ≡-isDecEquivalence-These = isDecEquivalence (≡-dec _≟_ _≟_)
