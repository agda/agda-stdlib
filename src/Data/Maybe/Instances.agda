------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Maybe
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Maybe.Instances where

open import Data.Maybe.Effectful
import Data.Maybe.Effectful.Transformer as Trans

instance
  -- Maybe
  maybeFunctor = functor
  maybeApplicative = applicative
  maybeApplicativeZero = applicativeZero
  maybeAlternative = alternative
  maybeMonad = monad
  maybeMonadZero = monadZero
  maybeMonadPlus = monadPlus
  -- MaybeT
  maybeTFunctor = λ {ℓ} {M} {{inst}} → Trans.functor {ℓ} {M} inst
  maybeTApplicative = λ {ℓ} {M} {{inst}} → Trans.applicative {ℓ} {M} inst
  maybeTMonad = λ {ℓ} {M} {{inst}} → Trans.monad {ℓ} {M} inst
  maybeTMonadT = λ {ℓ} {M} {{inst}} → Trans.monadT {ℓ} {M} inst
