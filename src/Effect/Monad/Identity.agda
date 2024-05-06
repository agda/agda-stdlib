------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of the identity function
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad.Identity where

open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad; module Join)
open import Effect.Comonad using (RawComonad)
open import Function.Base using (id; _∘′_; _|>′_; _$′_; flip)
open import Level using (Level)

private
  variable
    a : Level
    A : Set a

record Identity (A : Set a) : Set a where
  constructor mkIdentity
  field runIdentity : A
open Identity public

functor : RawFunctor {a} Identity
functor = record
  { _<$>_ = λ f a → mkIdentity (f (runIdentity a))
  }

applicative : RawApplicative {a} Identity
applicative = record
  { rawFunctor = functor
  ; pure = mkIdentity
  ; _<*>_  = λ f a → mkIdentity (runIdentity f $′ runIdentity a)
  }

monad : RawMonad {a} Identity
monad = record
  { rawApplicative = applicative
  ; _>>=_  = _|>′_ ∘′ runIdentity
  }

comonad : RawComonad {a} Identity
comonad = record
  { extract = runIdentity
  ; extend  = λ f a → mkIdentity (f a)
  }

join : Identity (Identity A) → Identity A
join = Join.join monad
