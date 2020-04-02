------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for TC
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.TypeChecking.Monad.Categorical where

open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Data.List.Base using ([])
open import Function.Base using (_∘_)
open import Level
open import Reflection.TypeChecking.Monad

private
  variable
    ℓ : Level

functor : RawFunctor {ℓ} TC
functor = record
  { _<$>_ = λ f mx → bindTC mx (return ∘ f)
  }

applicative : RawApplicative {ℓ} TC
applicative = record
  { pure = return
  ; _⊛_  = λ mf mx → bindTC mf λ f → bindTC mx (return ∘ f)
  }

applicativeZero : RawApplicativeZero {ℓ} TC
applicativeZero = record
  { applicative = applicative
  ; ∅           = typeError []
  }

alternative : RawAlternative {ℓ} TC
alternative = record
  { applicativeZero = applicativeZero
  ; _∣_             = catchTC
  }

monad : RawMonad {ℓ} TC
monad = record
  { return = return
  ; _>>=_  = bindTC
  }

monadZero : RawMonadZero {ℓ} TC
monadZero = record
  { monad           = monad
  ; applicativeZero = applicativeZero
  }

monadPlus : RawMonadPlus {ℓ} TC
monadPlus = record
  { monad       = monad
  ; alternative = alternative
  }
