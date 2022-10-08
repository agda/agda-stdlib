------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for IO
------------------------------------------------------------------------

{-# OPTIONS --without-K --guardedness #-}

open import IO.Base
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import IO.Effectful

instance
  ioFunctor = functor
  ioApplicative = applicative
  ioMonad = monad
