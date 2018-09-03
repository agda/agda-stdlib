------------------------------------------------------------------------
-- The Agda standard library
--
-- A categorical view of Stream
------------------------------------------------------------------------

module Codata.Stream.Categorical where

open import Data.Product using (<_,_>)
open import Codata.Stream
open import Function
open import Category.Functor
open import Category.Applicative
open import Category.Comonad

functor : ∀ {ℓ i} → RawFunctor {ℓ} (λ A → Stream A i)
functor = record { _<$>_ = λ f → map f }

applicative : ∀ {ℓ i} → RawApplicative {ℓ} (λ A → Stream A i)
applicative = record
  { pure = repeat
  ; _⊛_  = ap
  }

comonad : ∀ {ℓ} → RawComonad {ℓ} (λ A → Stream A _)
comonad = record
  { extract = head
  ; extend  = unfold ∘′ < tail ,_>
  }
