------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of Stream
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Stream.Effectful where

open import Data.Product using (<_,_>)
open import Codata.Sized.Stream
open import Effect.Functor
open import Effect.Applicative
open import Effect.Comonad
open import Function.Base

functor : ∀ {ℓ i} → RawFunctor {ℓ} (λ A → Stream A i)
functor = record { _<$>_ = λ f → map f }

applicative : ∀ {ℓ i} → RawApplicative {ℓ} (λ A → Stream A i)
applicative = record
  { rawFunctor = functor
  ; pure = repeat
  ; _<*>_  = ap
  }

comonad : ∀ {ℓ} → RawComonad {ℓ} (λ A → Stream A _)
comonad = record
  { extract = head
  ; extend  = unfold ∘′ < tail ,_>
  }
