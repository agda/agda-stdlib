------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of Colist
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Colist.Effectful where

open import Codata.Sized.Conat using (infinity)
open import Codata.Sized.Colist
open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative

functor : ∀ {ℓ i} → RawFunctor {ℓ} (λ A → Colist A i)
functor = record { _<$>_ = map }

applicative : ∀ {ℓ i} → RawApplicative {ℓ} (λ A → Colist A i)
applicative = record
  { rawFunctor = functor
  ; pure = replicate infinity
  ; _<*>_  = ap
  }

empty :  ∀ {ℓ i} → RawEmpty {ℓ} (λ A → Colist A i)
empty = record { empty = [] }

choice :  ∀ {ℓ i} → RawChoice {ℓ} (λ A → Colist A i)
choice = record { _<|>_ = _++_ }

applicativeZero : ∀ {ℓ i} → RawApplicativeZero {ℓ} (λ A → Colist A i)
applicativeZero = record
  { rawApplicative = applicative
  ; rawEmpty = empty
  }

alternative : ∀ {ℓ i} → RawAlternative {ℓ} (λ A → Colist A i)
alternative = record
  { rawApplicativeZero = applicativeZero
  ; rawChoice = choice
  }
