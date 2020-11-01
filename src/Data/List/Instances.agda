------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for List
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Instances where

open import Data.List.Categorical
open import Data.List.Properties
  using (≡-dec)
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.TypeClasses

instance
  listFunctor = functor
  listApplicative = applicative
  listApplicativeZero = applicativeZero
  listAlternative = alternative
  listMonad = monad
  listMonadZero = monadZero
  listMonadPlus = monadPlus
  listMonadT = λ {ℓ} {M} {{inst}} → monadT {ℓ} {M} inst

  ≡-isDecEquivalence-List = λ {a} {A} {{≡-isDecEquivalence-A}} → isDecEquivalence (≡-dec {a} {A} (_≟_ {{≡-isDecEquivalence-A}}))
