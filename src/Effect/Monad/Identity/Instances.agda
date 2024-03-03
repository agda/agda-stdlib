------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Identity
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad.Identity.Instances where

open import Effect.Monad.Identity

instance
  identityFunctor = functor
  identityApplicative = applicative
  identityMonad = monad
  identityComonad = comonad
