------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of Delay
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Delay.Effectful where

open import Codata.Sized.Delay
  using (Delay; now; never; later; map; bind; zipWith; alignWith)
open import Function.Base using (id)
open import Effect.Choice using (RawChoice)
open import Effect.Empty using (RawEmpty)
open import Effect.Functor using (RawFunctor)
open import Effect.Applicative
  using (RawApplicative; RawApplicativeZero; RawAlternative)
open import Effect.Monad using (RawMonad; RawMonadZero)
open import Data.These using (leftMost)

functor : ∀ {i ℓ} → RawFunctor {ℓ} (λ A → Delay A i)
functor = record { _<$>_ = λ f → map f }

module Sequential where

  applicative : ∀ {i ℓ} → RawApplicative {ℓ} (λ A → Delay A i)
  applicative = record
    { rawFunctor = functor
    ; pure = now
    ; _<*>_  = λ df da → bind df (λ f → map f da)
    }

  empty : ∀ {i ℓ} → RawEmpty {ℓ} (λ A → Delay A i)
  empty = record { empty = never }

  applicativeZero : ∀ {i ℓ} → RawApplicativeZero {ℓ} (λ A → Delay A i)
  applicativeZero = record
    { rawApplicative = applicative
    ; rawEmpty = empty
    }

  monad : ∀ {i ℓ} → RawMonad {ℓ} (λ A → Delay A i)
  monad = record
    { rawApplicative = applicative
    ; _>>=_  = bind
    }

  monadZero : ∀ {i ℓ} → RawMonadZero {ℓ} (λ A → Delay A i)
  monadZero = record
    { rawMonad = monad
    ; rawEmpty = empty
    }

module Zippy where

  applicative : ∀ {i ℓ} → RawApplicative {ℓ} (λ A → Delay A i)
  applicative = record
    { rawFunctor = functor
    ; pure = now
    ; _<*>_  = zipWith id
    }

  empty : ∀ {i ℓ} → RawEmpty {ℓ} (λ A → Delay A i)
  empty = record { empty = never }

  applicativeZero : ∀ {i ℓ} → RawApplicativeZero {ℓ} (λ A → Delay A i)
  applicativeZero = record
    { rawApplicative = applicative
    ; rawEmpty = empty
    }

  choice : ∀ {i ℓ} → RawChoice {ℓ} (λ A → Delay A i)
  choice = record { _<|>_ = alignWith leftMost }

  alternative : ∀ {i ℓ} → RawAlternative {ℓ} (λ A → Delay A i)
  alternative = record
    { rawApplicativeZero = applicativeZero
    ; rawChoice = choice
    }
