------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of Stream
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Stream.Effectful where

open import Data.Product.Base using (<_,_>)
open import Codata.Sized.Stream using
  (Stream; _∷_; _++_; _⁺++_; map; repeat; ap; head; unfold; tail)
open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)
open import Effect.Comonad using (RawComonad)
open import Function.Base using (_∘′_)

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
