------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Identity
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Identity.Instances where

open import Function.Identity.Effectful

instance
  identityFunctor = functor
  identityApplicative = applicative
  identityMonad = monad
  identityComonad = comonad
