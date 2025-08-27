------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of Covec
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Covec.Effectful where

open import Codata.Sized.Conat using (Conat; zero; suc)
open import Codata.Sized.Covec using (Covec; _∷_; []; map; replicate; ap)
open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)

functor : ∀ {ℓ i n} → RawFunctor {ℓ} (λ A → Covec A n i)
functor = record { _<$>_ = map }

applicative : ∀ {ℓ i n} → RawApplicative {ℓ} (λ A → Covec A n i)
applicative = record
  { rawFunctor = functor
  ; pure = replicate _
  ; _<*>_  = ap
  }
