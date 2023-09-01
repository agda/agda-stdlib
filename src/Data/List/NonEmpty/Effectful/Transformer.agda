------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of List
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.NonEmpty.Effectful.Transformer where

open import Data.List.NonEmpty.Base as List⁺ using (List⁺; _∷_)
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Base
open import Level using (Level)

import Data.List.NonEmpty.Effectful as List⁺

private
  variable
    f g : Level
    M : Set f → Set g

------------------------------------------------------------------------
-- List⁺ monad transformer

record List⁺T (M : Set f → Set g) (A : Set f) : Set g where
  constructor mkList⁺T
  field runList⁺T : M (List⁺ A)
open List⁺T public

functor : RawFunctor M → RawFunctor {f} (List⁺T M)
functor M = record
  { _<$>_ = λ f → mkList⁺T ∘′ (List⁺.map f <$>_) ∘′ runList⁺T
  } where open RawFunctor M

applicative : RawApplicative M → RawApplicative {f} (List⁺T M)
applicative M = record
  { rawFunctor = functor rawFunctor
  ; pure = mkList⁺T ∘′ pure ∘′ List⁺.[_]
  ; _<*>_  = λ mf ma → mkList⁺T (List⁺.ap <$> runList⁺T mf <*> runList⁺T ma)
  } where open RawApplicative M

monad : RawMonad M → RawMonad (List⁺T M)
monad M = record
  { rawApplicative = applicative rawApplicative
  ; _>>=_ = λ mas f → mkList⁺T $ do
                       as ← runList⁺T mas
                       List⁺.concat <$> mapM (runList⁺T ∘′ f) as
  } where open RawMonad M; open List⁺.TraversableM M

monadT : RawMonadT {f} {g} List⁺T
monadT M = record
  { lift = mkList⁺T ∘′ (List⁺.[_] <$>_)
  ; rawMonad = monad M
  } where open RawMonad M
