------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for TC
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.TypeChecking.Monad.Instances where

open import Reflection.TypeChecking.Monad.Categorical

instance
  tcFunctor = functor
  tcApplicative = applicative
  tcApplicativeZero = applicativeZero
  tcAlternative = alternative
  tcMonad = monad
  tcMonadZero = monadZero
  tcMonadPlus = monadPlus
