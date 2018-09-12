------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed unary relations
------------------------------------------------------------------------

module Relation.Unary.Indexed  where

open import Data.Product using (∃; _×_)
open import Level
open import Relation.Nullary using (¬_)

Pred : ∀ {i a} {I : Set i} → (I → Set a) → (ℓ : Level) → Set _
Pred A ℓ = ∀ {i} → A i → Set ℓ

module _ {i a} {I : Set i} {A : I → Set a} where

  _∈_ : ∀ {ℓ} → (∀ i → A i) → Pred A ℓ → Set _
  x ∈ P = ∀ i → P (x i)

  _∉_ : ∀ {ℓ} → (∀ i → A i) → Pred A ℓ → Set _
  t ∉ P = ¬ (t ∈ P)
