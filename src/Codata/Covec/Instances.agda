------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Covec
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Codata.Covec.Instances where

open import Codata.Covec.Categorical

instance
  covecFunctor = functor
  covecApplicative = applicative
