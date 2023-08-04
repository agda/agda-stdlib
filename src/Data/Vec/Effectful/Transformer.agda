------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of Vec
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Effectful.Transformer where

open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Base
open import Level

import Data.Vec.Effectful as Vec

private
  variable
    f g : Level
    n : ℕ
    M : Set f → Set g

------------------------------------------------------------------------
-- Vec monad transformer

record VecT (n : ℕ) (M : Set f → Set g) (A : Set f) : Set g where
  constructor mkVecT
  field runVecT : M (Vec A n)
open VecT public

functor : RawFunctor M → RawFunctor {f} (VecT n M)
functor M = record
  { _<$>_ = λ f → mkVecT ∘′ (Vec.map f <$>_) ∘′ runVecT
  } where open RawFunctor M

applicative : RawApplicative M → RawApplicative {f} (VecT n M)
applicative M = record
  { rawFunctor = functor rawFunctor
  ; pure = mkVecT ∘′ pure ∘′ Vec.replicate
  ; _<*>_  = λ mf ma → mkVecT (Vec.zipWith _$_ <$> runVecT mf <*> runVecT ma)
  } where open RawApplicative M

monad : {M : Set f → Set g} → RawMonad M → RawMonad (VecT n M)
monad {f} {g} M = record
  { rawApplicative = applicative rawApplicative
  ; _>>=_ = λ ma k → mkVecT $ do
                      a ← runVecT ma
                      bs ← mapM {a = f} (runVecT ∘′ k) a
                      pure (Vec.DiagonalBind.join bs)
  } where open RawMonad M; open Vec.TraversableM {m = f} {n = g} M

monadT : RawMonadT {f} {g} (VecT n)
monadT M = record
  { lift = mkVecT ∘′ (Vec.replicate <$>_)
  ; rawMonad = monad M
  } where open RawMonad M
