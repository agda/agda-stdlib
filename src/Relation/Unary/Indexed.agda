------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed unary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Unary.Indexed  where

open import Data.Product using (∃; _×_)
open import Level
open import Relation.Nullary using (¬_)

IPred : ∀ {i a} {I : Set i} → (I → Set a) → (ℓ : Level) → Set _
IPred A ℓ = ∀ {i} → A i → Set ℓ

module _ {i a} {I : Set i} {A : I → Set a} where

  _∈_ : ∀ {ℓ} → (∀ i → A i) → IPred A ℓ → Set _
  x ∈ P = ∀ i → P (x i)

  _∉_ : ∀ {ℓ} → (∀ i → A i) → IPred A ℓ → Set _
  t ∉ P = ¬ (t ∈ P)
