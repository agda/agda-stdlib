------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for IO
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module IO.Instances where

open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)
open import IO.Base using (IO)
open import IO.Effectful using (functor; applicative; monad)

instance
  ioFunctor = functor
  ioApplicative = applicative
  ioMonad = monad
