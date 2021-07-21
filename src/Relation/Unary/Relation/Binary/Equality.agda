------------------------------------------------------------------------
-- The Agda standard library
--
-- Equality of unary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Unary.Relation.Binary.Equality where

open import Data.Product using (Σ; _,_; swap; zip′)
open import Function.Base using (id)
open import Level using (Level)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Unary using (_≐_; _≐′_)

private
  variable
    a ℓ₁ ℓ₂ : Level
    A : Set a

≐-isEquivalence : IsEquivalence (_≐_ {A = A} {ℓ₁})
≐-isEquivalence = record
  { refl = id , id
  ; sym = swap
  ; trans = zip′ (λ P⊆Q Q⊆R {_} Px → Q⊆R (P⊆Q Px)) (λ Q⊆P R⊆Q {_} Rx → Q⊆P (R⊆Q Rx))
  }

≐′-isEquivalence : IsEquivalence (_≐′_ {A = A} {ℓ₁})
≐′-isEquivalence = record
  { refl = (λ _ → id) , λ _ → id
  ; sym = swap
  ; trans = zip′ (λ P⊆Q Q⊆R a a∈P → Q⊆R a (P⊆Q a a∈P)) λ Q⊆P R⊆Q a a∈R → Q⊆P a (R⊆Q a a∈R)
  }
