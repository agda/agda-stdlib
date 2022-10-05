------------------------------------------------------------------------
-- The Agda standard library
--
-- The state monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}


module Effect.Monad.State where

open import Data.Product
open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Base
open import Function.Identity.Effectful as Id using (Identity)
open import Level

import Effect.Monad.State.Transformer as Trans

private
  variable
    s : Level
    S A : Set s

------------------------------------------------------------------------
-- Re-export the state monad operations

open Trans public
  using (RawMonadState)

------------------------------------------------------------------------
-- State monad

State : (S : Set s) (A : Set s) → Set s
State S = Trans.StateT S Identity

runState : State S A → S → S × A
runState = Trans.runStateT

evalState : State S A → S → A
evalState = Trans.evalStateT Id.functor

execState : State S A → S → S
execState = Trans.execStateT Id.functor

------------------------------------------------------------------------
-- Structure

functor : RawFunctor (State S)
functor = Trans.functor Id.functor

applicative : RawApplicative (State S)
applicative = Trans.applicative Id.monad

monad : RawMonad (State S)
monad = Trans.monad Id.monad

------------------------------------------------------------------------
-- State monad specifics

monadState : RawMonadState S (State S)
monadState = Trans.monadState Id.monad
