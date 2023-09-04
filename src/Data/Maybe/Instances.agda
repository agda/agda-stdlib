------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for Maybe
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

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
  maybeTFunctor = λ {f} {g} {M} {{inst}} → Trans.functor {f} {g} {M} inst
  maybeTApplicative = λ {f} {g} {M} {{inst}} → Trans.applicative {f} {g} {M} inst
  maybeTMonad = λ {f} {g} {M} {{inst}} → Trans.monad {f} {g} {M} inst
  maybeTMonadT = λ {f} {g} {M} {{inst}} → Trans.monadT {f} {g} {M} inst
