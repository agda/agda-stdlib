------------------------------------------------------------------------
-- The Agda standard library
--
-- The reader monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level

module Effect.Monad.Reader where

open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Identity.Effectful as Id using (Identity)
open import Level using (Level)

import Effect.Monad.Reader.Transformer as Trans

private
  variable
    r : Level
    R : Set r

------------------------------------------------------------------------
-- Re-export the monad reader operations

open Trans public
  using (RawMonadReader)

------------------------------------------------------------------------
-- Reader monad

Reader : (R A : Set r) → Set r
Reader R = Trans.ReaderT R Identity

------------------------------------------------------------------------
-- Structure

functor : RawFunctor (Reader R)
functor = Trans.functor Id.functor

applicative : RawApplicative (Reader R)
applicative = Trans.applicative Id.applicative

monad : RawMonad (Reader R)
monad = Trans.monad Id.monad

------------------------------------------------------------------------
-- Reader monad specifics

monadReader : RawMonadReader R (Reader R)
monadReader = Trans.monadReader Id.monad
