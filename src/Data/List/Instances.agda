------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for List
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Instances where

open import Data.List.Base
open import Data.List.Categorical
open import Data.List.Properties
  using (≡-dec)
open import Level
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.TypeClasses

private
  variable
    a : Level
    A : Set a

instance
  listFunctor = functor
  listApplicative = applicative
  listApplicativeZero = applicativeZero
  listAlternative = alternative
  listMonad = monad
  listMonadZero = monadZero
  listMonadPlus = monadPlus
  listMonadT = λ {ℓ} {M} {{inst}} → monadT {ℓ} {M} inst

  List-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → IsDecEquivalence {A = List A} _≡_
  List-≡-isDecEquivalence = isDecEquivalence (≡-dec _≟_)
