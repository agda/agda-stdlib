------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of IO
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module IO.Effectful where

open import Level using (Level; _⊔_)
open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)

open import IO.Base

private
  variable
    f : Level

------------------------------------------------------------------------
-- Structure

functor : RawFunctor {f} IO
functor = record { _<$>_ = _<$>_ }

applicative : RawApplicative {f} IO
applicative = record
  { rawFunctor = functor
  ; pure = pure
  ; _<*>_ = _<*>_
  }

monad : RawMonad {f} IO
monad = record
  { rawApplicative = applicative
  ; _>>=_ = _>>=_
  }
