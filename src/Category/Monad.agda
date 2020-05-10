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
open import Data.Unit.Polymorphic
open import Level

private
  variable
    f : Level

RawMonad : (Set f → Set f) → Set _
RawMonad {f} M = RawIMonad {I = ⊤ {f}} (λ _ _ → M)

RawMonadT : (T : (Set f → Set f) → (Set f → Set f)) → Set _
RawMonadT {f} T = RawIMonadT {I = ⊤ {f}} (λ M _ _ → T (M _ _))

RawMonadZero : (Set f → Set f) → Set _
RawMonadZero {f} M = RawIMonadZero {I = ⊤ {f}} (λ _ _ → M)

RawMonadPlus : (Set f → Set f) → Set _
RawMonadPlus {f} M = RawIMonadPlus {I = ⊤ {f}} (λ _ _ → M)

module RawMonad {M : Set f → Set f} (Mon : RawMonad M) where
  open RawIMonad Mon public

module RawMonadZero {M : Set f → Set f}(Mon : RawMonadZero M) where
  open RawIMonadZero Mon public

module RawMonadPlus {M : Set f → Set f} (Mon : RawMonadPlus M) where
  open RawIMonadPlus Mon public
