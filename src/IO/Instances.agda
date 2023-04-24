------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for IO
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module IO.Instances where

open import IO.Base
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import IO.Effectful

instance
  ioFunctor = functor
  ioApplicative = applicative
  ioMonad = monad
