------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Stream
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Stream.Instances where

open import Codata.Stream.Categorical

instance
  streamFunctor = functor
  streamApplicative = applicative
  streamComonad = comonad
