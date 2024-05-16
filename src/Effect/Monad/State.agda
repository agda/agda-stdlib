------------------------------------------------------------------------
-- The Agda standard library
--
-- The state monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad.State where

open import Data.Product.Base using (_×_)
open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad; module Join)
open import Effect.Monad.Identity as Id using (Identity; runIdentity)
open import Level using (Level)

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
runState ma s = runIdentity (Trans.runStateT ma s)

evalState : State S A → S → A
evalState ma s = runIdentity (Trans.evalStateT Id.functor ma s)

execState : State S A → S → S
execState ma s = runIdentity (Trans.execStateT Id.functor ma s)

------------------------------------------------------------------------
-- Structure

functor : RawFunctor (State S)
functor = Trans.functor Id.functor

applicative : RawApplicative (State S)
applicative = Trans.applicative Id.monad

monad : RawMonad (State S)
monad = Trans.monad Id.monad

join : State S (State S A) → State S A
join = Join.join monad

------------------------------------------------------------------------
-- State monad specifics

monadState : RawMonadState S (State S)
monadState = Trans.monadState Id.monad
