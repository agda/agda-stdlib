------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Vec
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Instances where

open import Data.Vec.Base using (Vec)
open import Data.Vec.Effectful using (functor; applicative)
open import Data.Vec.Properties using (≡-dec)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.TypeClasses using (IsDecEquivalence; _≟_)

private
  variable
    a : Level
    A : Set a

instance
  vecFunctor = functor
  vecApplicative = applicative

  Vec-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → ∀ {n} → IsDecEquivalence {A = Vec A n} _≡_
  Vec-≡-isDecEquivalence = isDecEquivalence (≡-dec _≟_)
