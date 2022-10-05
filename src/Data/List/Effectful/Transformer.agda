------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of List
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Effectful.Transformer where

open import Data.List.Base as List using (List; []; _∷_)
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Base
open import Level

import Data.List.Effectful as List

private
  variable
    a b f : Level
    A : Set a
    B : Set b
    M : Set f → Set f

------------------------------------------------------------------------
-- List monad transformer

record ListT (M : Set f → Set f) (A : Set f) : Set f where
  constructor mkListT
  field runListT : M (List A)
open ListT public

functor : RawFunctor M → RawFunctor {f} (ListT M)
functor M = record
  { _<$>_ = λ f → mkListT ∘′ (List.map f <$>_) ∘′ runListT
  } where open RawFunctor M

applicative : RawApplicative M → RawApplicative {f} (ListT M)
applicative M = record
  { rawFunctor = functor rawFunctor
  ; pure = mkListT ∘′ pure ∘′ List.[_]
  ; _<*>_  = λ mf ma → mkListT (List.ap <$> runListT mf <*> runListT ma)
  } where open RawApplicative M

monad : RawMonad M → RawMonad (ListT M)
monad M = record
  { rawApplicative = applicative rawApplicative
  ; _>>=_ = λ mas f → mkListT $ do
                       as ← runListT mas
                       List.concat <$> mapM (runListT ∘′ f) as
  } where open RawMonad M; open List.TraversableM M

monadT : RawMonadT {f} ListT
monadT M = record
  { lift = mkListT ∘′ (List.[_] <$>_)
  ; rawMonad = monad M
  } where open RawMonad M
