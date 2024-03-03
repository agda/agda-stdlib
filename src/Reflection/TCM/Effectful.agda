------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for TC
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.TCM.Effectful where

open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Data.List.Base using ([])
open import Function.Base using (_∘_)
open import Level

open import Reflection.TCM

private
  variable
    ℓ : Level

functor : RawFunctor {ℓ} TC
functor = record
  { _<$>_ = λ f mx → bindTC mx (pure ∘ f)
  }

applicative : RawApplicative {ℓ} TC
applicative = record
  { rawFunctor = functor
  ; pure = pure
  ; _<*>_  = λ mf mx → bindTC mf λ f → bindTC mx (pure ∘ f)
  }

empty : RawEmpty {ℓ} TC
empty = record { empty = typeError [] }

applicativeZero : RawApplicativeZero {ℓ} TC
applicativeZero = record
  { rawApplicative = applicative
  ; rawEmpty = empty
  }

choice : RawChoice {ℓ} TC
choice = record { _<|>_ = catchTC }

alternative : RawAlternative {ℓ} TC
alternative = record
  { rawApplicativeZero = applicativeZero
  ; rawChoice = choice
  }

monad : RawMonad {ℓ} TC
monad = record
  { rawApplicative = applicative
  ; _>>=_  = bindTC
  }

monadZero : RawMonadZero {ℓ} TC
monadZero = record
  { rawMonad = monad
  ; rawEmpty = empty
  }

monadPlus : RawMonadPlus {ℓ} TC
monadPlus = record
  { rawMonadZero = monadZero
  ; rawChoice = choice
  }
