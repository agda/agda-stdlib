------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Maybe
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Maybe.Instances where

open import Data.Maybe.Categorical

instance
  maybeFunctor = functor
  maybeApplicative = applicative
  maybeApplicativeZero = applicativeZero
  maybeAlternative = alternative
  maybeMonad = monad
  maybeMonadZero = monadZero
  maybeMonadPlus = monadPlus
  maybeMonadT = λ {ℓ} {M} {{inst}} → monadT {ℓ} {M} inst
