------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Identity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Identity.Instances where

open import Function.Identity.Effectful

instance
  identityFunctor = functor
  identityApplicative = applicative
  identityMonad = monad
  identityComonad = comonad
