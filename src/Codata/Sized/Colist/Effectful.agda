------------------------------------------------------------------------
-- The Agda standard library
--
-- An effectful view of Colist
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Colist.Effectful where

open import Codata.Sized.Conat using (infinity)
open import Codata.Sized.Colist
open import Effect.Functor
open import Effect.Applicative

functor : ∀ {ℓ i} → RawFunctor {ℓ} (λ A → Colist A i)
functor = record { _<$>_ = map }

applicative : ∀ {ℓ i} → RawApplicative {ℓ} (λ A → Colist A i)
applicative = record
  { pure = replicate infinity
  ; _⊛_  = ap
  }
