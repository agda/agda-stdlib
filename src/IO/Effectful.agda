------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of IO
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module IO.Effectful where

open import Level
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad

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
