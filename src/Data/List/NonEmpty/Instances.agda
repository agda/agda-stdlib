------------------------------------------------------------------------
-- The Agda standard library
--
-- Typeclass instances for List⁺
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.NonEmpty.Instances where

open import Data.List.NonEmpty.Effectful
  using (functor; applicative; monad; comonad)
import Data.List.NonEmpty.Effectful.Transformer as Trans
  using (functor; applicative; monad; monadT)
instance
  -- List⁺ instances
  nonEmptyListFunctor = functor
  nonEmptyListApplicative = applicative
  nonEmptyListMonad = monad
  nonEmptyListComonad = comonad
  -- List⁺T instances
  nonEmptyListTFunctor = λ {f} {g} {M} {{inst}} → Trans.functor {f} {g} {M} inst
  nonEmptyListTApplicative = λ {f} {g} {M} {{inst}} → Trans.applicative {f} {g} {M} inst
  nonEmptyListTMonad = λ {f} {g} {M} {{inst}} → Trans.monad {f} {g} {M} inst
  nonEmptyListTMonadT = λ {f} {g} {M} {{inst}} → Trans.monadT {f} {g} {M} inst
