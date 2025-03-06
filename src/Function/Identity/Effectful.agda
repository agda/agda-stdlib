------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of the identity function
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Identity.Effectful where

open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)
open import Effect.Comonad using (RawComonad)
open import Function.Base using (id; _∘′_; _|>′_; _$′_; flip)
open import Level using (Level; _⊔_)

private
  variable
    ℓ : Level

Identity : (A : Set ℓ) → Set ℓ
Identity A = A

functor : RawFunctor {ℓ} Identity
functor = record
  { _<$>_ = id
  }

applicative : RawApplicative {ℓ} Identity
applicative = record
  { rawFunctor = functor
  ; pure = id
  ; _<*>_  = _$′_
  }

monad : RawMonad {ℓ} Identity
monad = record
  { rawApplicative = applicative
  ; _>>=_  = _|>′_
  }

comonad : RawComonad {ℓ} Identity
comonad = record
  { extract = id
  ; extend  = _$′_
  }
