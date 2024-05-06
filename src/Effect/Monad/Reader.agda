------------------------------------------------------------------------
-- The Agda standard library
--
-- The reader monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad.Reader where

open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad; module Join)
open import Effect.Monad.Identity as Id using (Identity; runIdentity)
open import Level using (Level)

import Effect.Monad.Reader.Transformer as Trans

private
  variable
    r : Level
    R A : Set r

------------------------------------------------------------------------
-- Re-export the monad reader operations

open Trans public
  using (RawMonadReader)

------------------------------------------------------------------------
-- Reader monad

Reader : (R A : Set r) → Set r
Reader R = Trans.ReaderT R Identity

runReader : Reader R A → R → A
runReader mr r = runIdentity (Trans.runReaderT mr r)

------------------------------------------------------------------------
-- Structure

functor : RawFunctor (Reader R)
functor = Trans.functor Id.functor

applicative : RawApplicative (Reader R)
applicative = Trans.applicative Id.applicative

monad : RawMonad (Reader R)
monad = Trans.monad Id.monad

join : Reader R (Reader R A) → Reader R A
join = Join.join monad

------------------------------------------------------------------------
-- Reader monad specifics

monadReader : RawMonadReader R (Reader R)
monadReader = Trans.monadReader Id.monad
