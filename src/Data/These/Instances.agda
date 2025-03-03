------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for These
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.These.Instances where

open import Data.These.Base using (These; this; that; these)
open import Data.These.Properties using (≡-dec)
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
  These-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → {{IsDecEquivalence {A = B} _≡_}} → IsDecEquivalence {A = These A B} _≡_
  These-≡-isDecEquivalence = isDecEquivalence (≡-dec _≟_ _≟_)
