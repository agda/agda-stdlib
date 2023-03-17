------------------------------------------------------------------------
-- The Agda standard library
--
-- The writer monad
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Effect.Monad.Writer where

open import Algebra using (RawMonoid)
open import Data.Product using (_×_)
open import Effect.Applicative
open import Effect.Choice
open import Effect.Empty
open import Effect.Functor
open import Effect.Monad
open import Effect.Monad.Identity as Id using (Identity; runIdentity)
open import Function.Base using (_∘′_)
open import Level using (Level)

import Effect.Monad.Writer.Transformer as Trans

private
  variable
    w ℓ : Level
    A : Set w
    𝕎 : RawMonoid w ℓ

------------------------------------------------------------------------
-- Re-export the monad writer operations

open Trans public
  using (RawMonadWriter)

------------------------------------------------------------------------
-- Writer monad

Writer : (𝕎 : RawMonoid w ℓ) (A : Set w) → Set w
Writer 𝕎 = Trans.WriterT 𝕎 Identity

functor : RawFunctor (Writer 𝕎)
functor = Trans.functor Id.functor

module _ {𝕎 : RawMonoid w ℓ} where

  open RawMonoid 𝕎 renaming (Carrier to W)

  runWriter : Writer 𝕎 A → W × A
  runWriter ma = runIdentity (Trans.runWriterT ma ε)

  applicative : RawApplicative (Writer 𝕎)
  applicative = Trans.applicative Id.applicative

  monad : RawMonad (Writer 𝕎)
  monad = Trans.monad Id.monad

  ----------------------------------------------------------------------
  -- Writer monad specifics

  monadWriter : RawMonadWriter 𝕎 (Writer 𝕎)
  monadWriter = Trans.monadWriter Id.monad
