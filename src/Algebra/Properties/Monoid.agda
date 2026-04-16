------------------------------------------------------------------------
-- The Agda standard library
--
-- Equational reasoning for monoids
-- (Utilities for identity and cancellation reasoning, extending semigroup reasoning)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)

module Algebra.Properties.Monoid {o ℓ} (M : Monoid o ℓ) where

open import Function using (_∘_)

open Monoid M
  using (Carrier; _∙_; ε; _≈_; refl; sym; trans; setoid
        ; ∙-cong; ∙-congˡ; ∙-congʳ; isMagma
        ; assoc; semigroup; identity; identityˡ; identityʳ)

open import Algebra.Consequences.Setoid setoid using (identity⇒central)
open import Algebra.Definitions _≈_ using (Central)
open import Relation.Binary.Reasoning.Setoid setoid

private
  variable
    a b c d : Carrier

------------------------------------------------------------------------
-- Re-export `Semigroup` properties

open import Algebra.Properties.Semigroup semigroup public

------------------------------------------------------------------------
-- Properties of identity

ε-unique : ∀ a → (∀ b → b ∙ a ≈ b) → a ≈ ε
ε-unique a b∙a≈b = trans (sym (identityˡ a)) (b∙a≈b ε)

ε-central : Central _∙_ ε
ε-central = identity⇒central {_∙_ = _∙_} identity

module _ (a≈ε : a ≈ ε) where
  elimʳ : ∀ b → b ∙ a ≈ b
  elimʳ = trans (∙-congˡ a≈ε) ∘ identityʳ

  elimˡ : ∀ b → a ∙ b ≈ b
  elimˡ = trans (∙-congʳ a≈ε) ∘ identityˡ

  introʳ : ∀ b → b ≈ b ∙ a
  introʳ = sym ∘ elimʳ

  introˡ : ∀ b → b ≈ a ∙ b
  introˡ = sym ∘ elimˡ

  introᶜ : ∀ c → b ∙ c ≈ b ∙ (a ∙ c)
  introᶜ c = trans (∙-congˡ (sym (identityˡ c))) (∙-congˡ (∙-congʳ (sym a≈ε)))

module _ (inv : a ∙ c ≈ ε) where

  cancelʳ : ∀ b → (b ∙ a) ∙ c ≈ b
  cancelʳ b = trans (uv≈w⇒xu∙v≈xw inv b) (identityʳ b)

  cancelˡ : ∀ b → a ∙ (c ∙ b) ≈ b
  cancelˡ b = trans (uv≈w⇒u∙vx≈wx inv b) (identityˡ b)

  insertˡ : ∀ b → b ≈ a ∙ (c ∙ b)
  insertˡ = sym ∘ cancelˡ

  insertʳ : ∀ b → b ≈ (b ∙ a) ∙ c
  insertʳ = sym ∘ cancelʳ

  cancelᶜ : ∀ b d → (b ∙ a) ∙ (c ∙ d) ≈ b ∙ d
  cancelᶜ b d = trans (uv≈w⇒xu∙vy≈x∙wy inv b d) (∙-congˡ (identityˡ d))

  insertᶜ : ∀ b d → b ∙ d ≈ (b ∙ a) ∙ (c ∙ d)
  insertᶜ = λ b d → sym (cancelᶜ b d)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.4

ε-comm = ε-central
{-# WARNING_ON_USAGE ε-comm
"Warning: ε-comm was deprecated in v2.4.
Please use ε-central instead."
#-}
