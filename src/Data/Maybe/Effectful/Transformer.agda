------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of Maybe
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Maybe.Effectful.Transformer where

open import Level
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; maybe)

open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad

import Data.Maybe.Effectful as Maybe
open import Function.Base

private
  variable
    f g : Level
    M : Set f → Set g

------------------------------------------------------------------------
-- Maybe monad transformer

record MaybeT (M : Set f → Set g) (A : Set f) : Set g where
  constructor mkMaybeT
  field runMaybeT : M (Maybe A)
open MaybeT public

------------------------------------------------------------------------
-- Structure

functor : RawFunctor M → RawFunctor {f} (MaybeT M)
functor M = record
  { _<$>_ = λ f → mkMaybeT ∘′ (Maybe.map f <$>_) ∘′ runMaybeT
  } where open RawFunctor M

applicative : RawApplicative M → RawApplicative {f} (MaybeT M)
applicative M = record
  { rawFunctor = functor rawFunctor
  ; pure       = mkMaybeT ∘′ pure ∘′ just
  ; _<*>_      = λ mf ma → mkMaybeT (Maybe.ap <$> runMaybeT mf <*> runMaybeT ma)
  } where open RawApplicative M

monad : RawMonad M → RawMonad {f} (MaybeT M)
monad M = record
  { rawApplicative = applicative rawApplicative
  ; _>>=_ = λ ma f → mkMaybeT $ do
              a ← runMaybeT ma
              maybe (runMaybeT ∘′ f) (pure nothing) a
  } where open RawMonad M

monadT : RawMonadT {f} {g} MaybeT
monadT {M = F} M = record
  { lift = mkMaybeT ∘′ (just <$>_)
  ; rawMonad = monad M
  } where open RawMonad M
