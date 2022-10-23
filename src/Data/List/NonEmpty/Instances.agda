------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for List⁺
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.NonEmpty.Instances where

open import Data.List.NonEmpty.Effectful

instance
  nonEmptyListFunctor = functor
  nonEmptyListApplicative = applicative
  nonEmptyListMonad = monad
  nonEmptyListComonad = comonad
  nonEmptyListMonadT = λ {ℓ} {M} {{inst}} → monadT {ℓ} {M} inst
