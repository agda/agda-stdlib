------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for TC
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.TCM.Instances where

open import Reflection.TCM.Effectful

instance
  tcFunctor = functor
  tcApplicative = applicative
  tcApplicativeZero = applicativeZero
  tcAlternative = alternative
  tcMonad = monad
  tcMonadZero = monadZero
  tcMonadPlus = monadPlus
