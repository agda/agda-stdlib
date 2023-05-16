------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of Covec
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Covec.Effectful where

open import Codata.Sized.Conat
open import Codata.Sized.Covec
open import Effect.Functor
open import Effect.Applicative

functor : ∀ {ℓ i n} → RawFunctor {ℓ} (λ A → Covec A n i)
functor = record { _<$>_ = map }

applicative : ∀ {ℓ i n} → RawApplicative {ℓ} (λ A → Covec A n i)
applicative = record
  { rawFunctor = functor
  ; pure = replicate _
  ; _<*>_  = ap
  }
