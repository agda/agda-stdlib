------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Identity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Effect.Monad.Identity.Instances where

open import Effect.Monad.Identity

instance
  identityFunctor = functor
  identityApplicative = applicative
  identityMonad = monad
  identityComonad = comonad
