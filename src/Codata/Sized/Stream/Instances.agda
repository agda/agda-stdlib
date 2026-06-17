------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Stream
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Codata.Sized.Stream.Instances where

open import Codata.Sized.Stream.Effectful using (functor; applicative; comonad)

instance
  streamFunctor = functor
  streamApplicative = applicative
  streamComonad = comonad
