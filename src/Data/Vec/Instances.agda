------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Vec
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Instances where

open import Data.Vec.Categorical
open import Data.Vec.Properties
  using (≡-dec)
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Data.Vec.Relation.Binary.Equality.DecPropositional
open import Relation.Binary.TypeClasses


instance
  vecFunctor = functor
  vecApplicative = applicative

  ≡-isDecEquivalence-Vec = λ {a} {A} {{≡-isDecEquivalence-A}} {n} → isDecEquivalence (≡-dec {a} {A} (_≟_ {{≡-isDecEquivalence-A}}) {n})
