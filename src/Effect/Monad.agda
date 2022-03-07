------------------------------------------------------------------------
-- The Agda standard library
--
-- Monads
------------------------------------------------------------------------

-- Note that currently the monad laws are not included here.

{-# OPTIONS --without-K --safe #-}

module Category.Monad where

open import Function
open import Category.Monad.Indexed
open import Data.Unit
open import Level

private
  variable
    f : Level

RawMonad : (Set f → Set f) → Set _
RawMonad M = RawIMonad {I = ⊤} (λ _ _ → M)

RawMonadT : (T : (Set f → Set f) → (Set f → Set f)) → Set _
RawMonadT T = RawIMonadT {I = ⊤} (λ M _ _ → T (M _ _))

RawMonadZero : (Set f → Set f) → Set _
RawMonadZero M = RawIMonadZero {I = ⊤} (λ _ _ → M)

RawMonadPlus : (Set f → Set f) → Set _
RawMonadPlus M = RawIMonadPlus {I = ⊤} (λ _ _ → M)

module RawMonad {M : Set f → Set f} (Mon : RawMonad M) where
  open RawIMonad Mon public

module RawMonadZero {M : Set f → Set f}(Mon : RawMonadZero M) where
  open RawIMonadZero Mon public

module RawMonadPlus {M : Set f → Set f} (Mon : RawMonadPlus M) where
  open RawIMonadPlus Mon public
