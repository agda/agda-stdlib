------------------------------------------------------------------------
-- The Agda standard library
--
-- Equational reasoning for monoids
-- (Utilities for identity and cancellation reasoning, extending semigroup reasoning)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)

module Algebra.Properties.Monoid.Reasoning {o ℓ} (M : Monoid o ℓ) where

open Monoid M
  using (Carrier; _∙_; _≈_; setoid; isMagma; semigroup; ε; sym; identityˡ
  ; identityʳ ; ∙-cong; refl; assoc; ∙-congˡ; ∙-congʳ; trans)
open import Relation.Binary.Reasoning.Setoid setoid

open import Algebra.Properties.Semigroup semigroup public

private
    variable
        a b c d : Carrier

module _ where
    id-unique : ∀ a → (∀ b → b ∙ a ≈ b) → a ≈ ε
    id-unique a b∙a≈b = trans (sym (identityˡ a)) (b∙a≈b ε)

    id-comm : ∀ a → a ∙ ε ≈ ε ∙ a
    id-comm a = trans (identityʳ a) (sym (identityˡ a))

    id-comm-sym : ∀ a → ε ∙ a ≈ a ∙ ε
    id-comm-sym a = sym (id-comm a)

module _ {a b : Carrier} (a≈ε : a ≈ ε) where
    elimʳ : ∀ b → b ∙ a ≈ b
    elimʳ b = trans (∙-congˡ a≈ε) (identityʳ b)

    elimˡ : ∀ b → a ∙ b ≈ b
    elimˡ b = trans (∙-congʳ a≈ε) (identityˡ b)

    introʳ : ∀ b → b ≈ b ∙ a
    introʳ b = sym (elimʳ b)

    introˡ : ∀ b → b ≈ a ∙ b
    introˡ b = sym (elimˡ b)

    introcenter : ∀ c → b ∙ c ≈ b ∙ (a ∙ c)
    introcenter c = trans (∙-congˡ (sym (identityˡ c))) (∙-congˡ (∙-congʳ (sym a≈ε)))

module _ {a c : Carrier} (inv : a ∙ c ≈ ε) where

  cancelʳ : ∀ b → (b ∙ a) ∙ c ≈ b
  cancelʳ b = trans (assoc b a c) (trans (∙-congˡ inv) (identityʳ b))

  cancelˡ : ∀ b → a ∙ (c ∙ b) ≈ b
  cancelˡ b = trans (sym (assoc a c b)) (trans (∙-congʳ inv) (identityˡ b))

  insertˡ : ∀ b → b ≈ a ∙ (c ∙ b)
  insertˡ b = sym (cancelˡ b)

  insertʳ : ∀ b → b ≈ (b ∙ a) ∙ c
  insertʳ b = sym (cancelʳ b)

  cancelInner : ∀ b d → (b ∙ a) ∙ (c ∙ d) ≈ b ∙ d
  cancelInner b d = trans (sym (assoc (b ∙ a) c d)) (∙-congʳ (cancelʳ b))

  insertInner : ∀ b d → b ∙ d ≈ (b ∙ a) ∙ (c ∙ d)
  insertInner b d = sym (cancelInner b d)

