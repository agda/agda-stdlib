------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Vec
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Instances where

open import Data.Vec.Base
open import Data.Vec.Categorical
open import Data.Vec.Properties
  using (≡-dec)
open import Level
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Data.Vec.Relation.Binary.Equality.DecPropositional
open import Relation.Binary.TypeClasses

private
  variable
    a : Level
    A : Set a

instance
  vecFunctor = functor
  vecApplicative = applicative

  Vec-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → ∀ {n} → IsDecEquivalence {A = Vec A n} _≡_
  Vec-≡-isDecEquivalence = isDecEquivalence (≡-dec _≟_)
