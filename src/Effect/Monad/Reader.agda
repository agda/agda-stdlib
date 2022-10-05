------------------------------------------------------------------------
-- The Agda standard library
--
-- The reader monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level

module Effect.Monad.Reader {r} (R : Set r) (a : Level) where

open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Applicative
open import Effect.Monad
open import Function.Identity.Effectful as Id using (Identity)

import Effect.Monad.Reader.Transformer R a as Trans

------------------------------------------------------------------------
-- Re-export the monad reader operations

open Trans public
  using (RawMonadReader)

------------------------------------------------------------------------
-- Reader monad

Reader : (A : Set (r ⊔ a)) → Set (r ⊔ a)
Reader = Trans.ReaderT 0ℓ Identity

------------------------------------------------------------------------
-- Structure

functor : RawFunctor Reader
functor = Trans.functor Id.functor

applicative : RawApplicative Reader
applicative = Trans.applicative Id.applicative

monad : RawMonad Reader
monad = Trans.monad Id.monad

------------------------------------------------------------------------
-- Reader monad specifics

monadReader : RawMonadReader Reader
monadReader = Trans.monadReader Id.monad
