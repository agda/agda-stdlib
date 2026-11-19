------------------------------------------------------------------------
-- The Agda standard library
--
-- Coprimality of ideals
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Bundles

module Algebra.Ideal.Coprimality {c ℓ} (R : Ring c ℓ) where

open Ring R hiding (sym)

open import Algebra.Ideal R
open import Data.Product.Base
open import Level
open import Relation.Binary.Reasoning.Setoid setoid

Coprime : ∀ {c₁ c₂ ℓ₁ ℓ₂} → Ideal c₁ ℓ₁ → Ideal c₂ ℓ₂ → Set (ℓ ⊔ c₁ ⊔ c₂)
Coprime I J = Σ[ (i , j) ∈ I.I.Carrierᴹ × J.I.Carrierᴹ ] I.ι i + J.ι j ≈ 1#
  where
    module I = Ideal I
    module J = Ideal J

sym : ∀ {c₁ c₂ ℓ₁ ℓ₂} {I : Ideal c₁ ℓ₁} {J : Ideal c₂ ℓ₂} → Coprime I J → Coprime J I
sym {I = I} {J = J} ((i , j) , p) = record
  { fst = j , i
  ; snd = begin
    J.ι j + I.ι i ≈⟨ +-comm (J.ι j) (I.ι i) ⟩
    I.ι i + J.ι j ≈⟨ p ⟩
    1#            ∎
  }
  where
    module I = Ideal I
    module J = Ideal J
