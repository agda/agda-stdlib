------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for TC
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.TCMonad.Instances where

open import Reflection.TCMonad

instance
  tcFunctor = functor
  tcApplicative = applicative
  tcApplicativeZero = applicativeZero
  tcAlternative = alternative
  tcMonad = monad
  tcMonadZero = monadZero
  tcMonadPlus = monadPlus
