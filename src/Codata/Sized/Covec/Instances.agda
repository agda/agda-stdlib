------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Covec
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Covec.Instances where

open import Codata.Sized.Covec.Effectful using (functor; applicative)

instance
  covecFunctor = functor
  covecApplicative = applicative
