------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Identity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Identity.Instances where

open import Function.Identity.Categorical

instance
  identityFunctor = functor
  identityApplicative = applicative
  identityMonad = monad
  identityComonad = comonad
