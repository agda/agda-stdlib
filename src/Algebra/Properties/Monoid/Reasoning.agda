------------------------------------------------------------------------
-- The Agda standard library
--
-- Equational reasoning for monoids
-- (Utilities for identity and cancellation reasoning, extending semigroup reasoning)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)
open import Algebra.Structures using (IsMagma)

module Algebra.Properties.Monoid.Reasoning {o ℓ} (M : Monoid o ℓ) where

open Monoid M
    using (Carrier; _∙_; _≈_; setoid; isMagma; semigroup; ε; sym; identityˡ
    ; identityʳ ; ∙-cong; refl; assoc; ∙-congˡ; ∙-congʳ; trans)
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Properties.Semigroup.Reasoning semigroup public

module Identity {a : Carrier } where
    id-unique : (∀ b → b ∙ a ≈ b) → a ≈ ε
    id-unique b∙a≈b = trans (sym (identityˡ a)) (b∙a≈b ε)

    id-comm : a ∙ ε ≈ ε ∙ a
    id-comm = trans (identityʳ a) (sym (identityˡ a))

    id-comm-sym : ε ∙ a ≈ a ∙ ε
    id-comm-sym = sym id-comm

open Identity public

module IntroElim {a b : Carrier} (a≈ε : a ≈ ε) where
    elimʳ : b ∙ a ≈ b
    elimʳ = trans (∙-congˡ a≈ε) (identityʳ b)

    elimˡ : a ∙ b ≈ b
    elimˡ = trans (∙-congʳ a≈ε) (identityˡ b)

    introʳ : a ≈ ε → b ≈ b ∙ a
    introʳ a≈ε = sym elimʳ

    introˡ : a ≈ ε → b ≈ a ∙ b
    introˡ a≈ε = sym elimˡ

    introcenter : ∀ c → b ∙ c ≈ b ∙ (a ∙ c)
    introcenter c = trans (∙-congˡ (sym (identityˡ c))) (∙-congˡ (∙-congʳ (sym a≈ε)))

open IntroElim public

module Cancellers {a b c : Carrier} (inv : a ∙ c ≈ ε) where

  cancelʳ : (b ∙ a) ∙ c ≈ b
  cancelʳ = trans (assoc b a c) (trans (∙-congˡ inv) (identityʳ b))

  cancelˡ : a ∙ (c ∙ b) ≈ b
  cancelˡ = trans (sym (assoc a c b)) (trans (∙-congʳ inv) (identityˡ b))

  insertˡ : b ≈ a ∙ (c ∙ b)
  insertˡ = sym cancelˡ

  insertʳ : b ≈ (b ∙ a) ∙ c
  insertʳ = sym cancelʳ

  cancelInner : ∀ {g} → (b ∙ a) ∙ (c ∙ g) ≈ b ∙ g
  cancelInner {g = g} = trans (sym (assoc (b ∙ a) c g)) (∙-congʳ cancelʳ)

  insertInner : ∀ {g} → b ∙ g ≈ (b ∙ a) ∙ (c ∙ g)
  insertInner = sym cancelInner
