------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of the identity function
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Effect.Monad.Identity where

open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Effect.Comonad
open import Function.Base using (id; _∘′_; _|>′_; flip)
open import Level

private
  variable
    ℓ : Level

record Identity (A : Set ℓ) : Set ℓ where
  constructor mkIdentity
  field runIdentity : A
open Identity public

functor : RawFunctor {ℓ} Identity
functor = record
  { _<$>_ = λ f x → mkIdentity (f (runIdentity x))
  }

applicative : RawApplicative {ℓ} Identity
applicative = record
  { rawFunctor = functor
  ; pure = mkIdentity
  ; _<*>_  = λ f x → mkIdentity (runIdentity f (runIdentity x))
  }

monad : RawMonad {ℓ} Identity
monad = record
  { rawApplicative = applicative
  ; _>>=_  = _|>′_ ∘′ runIdentity
  }

comonad : RawComonad {ℓ} Identity
comonad = record
  { extract = runIdentity
  ; extend  = λ f x → mkIdentity (x |>′ f)
  }
