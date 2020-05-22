------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for List⁺
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.NonEmpty.Instances where

open import Data.List.NonEmpty.Categorical

instance
  nonEmptyListFunctor = functor
  nonEmptyListApplicative = applicative
  nonEmptyListMonad = monad
  nonEmptyListComonad = comonad
  nonEmptyListMonadT = λ {ℓ} {M} {{inst}} → monadT {ℓ} {M} inst
