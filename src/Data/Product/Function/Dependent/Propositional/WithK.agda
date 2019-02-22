------------------------------------------------------------------------
-- The Agda standard library
--
-- Dependent product combinators for propositional equality
-- preserving functions
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Product.Function.Dependent.Propositional.WithK where

open import Data.Product
open import Data.Product.Function.Dependent.Setoid
open import Data.Product.Relation.Binary.Pointwise.Dependent
open import Data.Product.Relation.Binary.Pointwise.Dependent.WithK
open import Function.Equality using (_⟨$⟩_)
open import Function.Injection as Inj using (_↣_; module Injection)
open import Function.Inverse as Inv using (_↔_; module Inverse)
import Relation.Binary.HeterogeneousEquality as H

------------------------------------------------------------------------
-- Combinator for Injection

module _ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂}
         {b₁ b₂} {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
         where

  ↣ : ∀ (A₁↣A₂ : A₁ ↣ A₂) →
      (∀ {x} → B₁ x ↣ B₂ (Injection.to A₁↣A₂ ⟨$⟩ x)) →
      Σ A₁ B₁ ↣ Σ A₂ B₂
  ↣ A₁↣A₂ B₁↣B₂ =
    Inverse.injection Pointwise-≡↔≡ ⟨∘⟩
    injection (H.indexedSetoid B₂) A₁↣A₂
      (Inverse.injection (H.≡↔≅ B₂) ⟨∘⟩
       B₁↣B₂ ⟨∘⟩
       Inverse.injection (Inv.sym (H.≡↔≅ B₁))) ⟨∘⟩
    Inverse.injection (Inv.sym Pointwise-≡↔≡)
    where open Inj using () renaming (_∘_ to _⟨∘⟩_)
