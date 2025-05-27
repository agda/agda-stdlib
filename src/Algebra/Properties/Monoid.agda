------------------------------------------------------------------------
-- The Agda standard library
--
-- Equational reasoning for monoids
-- (Utilities for identity and cancellation reasoning, extending semigroup reasoning)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)
open import Function using (_∘_)

module Algebra.Properties.Monoid {o ℓ} (M : Monoid o ℓ) where

open Monoid M
  using (Carrier; _∙_; _≈_; setoid; isMagma; semigroup; ε; sym; identityˡ
  ; identityʳ ; ∙-cong; refl; assoc; ∙-congˡ; ∙-congʳ; trans)
open import Relation.Binary.Reasoning.Setoid setoid

open import Algebra.Properties.Semigroup semigroup public

private
    variable
        a b c d : Carrier

id-unique : ∀ a → (∀ b → b ∙ a ≈ b) → a ≈ ε
id-unique a b∙a≈b = trans (sym (identityˡ a)) (b∙a≈b ε)

id-comm : ∀ a → a ∙ ε ≈ ε ∙ a
id-comm a = trans (identityʳ a) (sym (identityˡ a))

id-comm-sym : ∀ a → ε ∙ a ≈ a ∙ ε
id-comm-sym = sym ∘ id-comm

module _ (a≈ε : a ≈ ε) where
    elimʳ : ∀ b → b ∙ a ≈ b
    elimʳ = trans (∙-congˡ a≈ε) ∘ identityʳ

    elimˡ : ∀ b → a ∙ b ≈ b
    elimˡ = trans (∙-congʳ a≈ε) ∘ identityˡ

    introʳ : ∀ b → b ≈ b ∙ a
    introʳ = sym ∘ elimʳ

    introˡ : ∀ b → b ≈ a ∙ b
    introˡ = sym ∘ elimˡ

    introcenter : ∀ c → b ∙ c ≈ b ∙ (a ∙ c)
    introcenter c = trans (∙-congˡ (sym (identityˡ c))) (∙-congˡ (∙-congʳ (sym a≈ε)))

module _ (inv : a ∙ c ≈ ε) where

  cancelʳ : ∀ b → (b ∙ a) ∙ c ≈ b
  cancelʳ b = trans (assoc b a c) (trans (∙-congˡ inv) (identityʳ b))

  cancelˡ : ∀ b → a ∙ (c ∙ b) ≈ b
  cancelˡ b = trans (sym (assoc a c b)) (trans (∙-congʳ inv) (identityˡ b))

  insertˡ : ∀ b → b ≈ a ∙ (c ∙ b)
  insertˡ = sym ∘ cancelˡ

  insertʳ : ∀ b → b ≈ (b ∙ a) ∙ c
  insertʳ = sym ∘ cancelʳ

  cancelInner : ∀ b d → (b ∙ a) ∙ (c ∙ d) ≈ b ∙ d
  cancelInner b d = trans (uv≈w⇒xu∙vy≈x∙wy inv b d) (∙-congˡ (identityˡ d))

  insertInner : ∀ b d → b ∙ d ≈ (b ∙ a) ∙ (c ∙ d)
  insertInner = λ b d → sym (cancelInner b d)

