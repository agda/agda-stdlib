------------------------------------------------------------------------
-- The Agda standard library
--
-- A categorical view of Delay
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Codata.Delay.Categorical where

open import Codata.Delay
open import Function
open import Category.Functor
open import Category.Applicative
open import Category.Monad

functor : ∀ {i ℓ} → RawFunctor {ℓ} (λ A → Delay A i)
functor = record { _<$>_ = λ f → map f }

module Sequential where

  applicative : ∀ {i ℓ} → RawApplicative {ℓ} (λ A → Delay A i)
  applicative = record
    { pure = now
    ; _⊛_  = λ df da → bind df (λ f → map f da)
    }

  monad : ∀ {i ℓ} → RawMonad {ℓ} (λ A → Delay A i)
  monad = record
    { return = now
    ; _>>=_  = bind
    }

  monadZero : ∀ {i ℓ} → RawMonadZero {ℓ} (λ A → Delay A i)
  monadZero = record
    { monad = monad
    ; ∅     = never
    }

module Zippy where

  applicative : ∀ {i ℓ} → RawApplicative {ℓ} (λ A → Delay A i)
  applicative = record
    { pure = now
    ; _⊛_  = zipWith id
    }

  -- We do not have `RawApplicativeZero` and `RawApplicativePlus` yet but here is what
  -- they would look like

  {-
  applicativeZero : ∀ {i ℓ} → RawApplicativeZero {ℓ} (λ A → Delay A i)
  applicativeZero = record
    { applicative = applicative
    ; ∅           = never
    }

  applicativePlus : ∀ {i ℓ} → RawApplicativeZero {ℓ} (λ A → Delay A i)
  applicativePlus = record
    { applicativeZero = applicativeZero
    ; _∣_             = alignWith leftMost
    }
  -}
