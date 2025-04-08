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
    using (Carrier; _∙_; _≈_; setoid; isMagma; semigroup; ε; sym; identityˡ; identityʳ
    ; ∙-cong; refl; assoc; ∙-congˡ; ∙-congʳ)
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Properties.Semigroup.Reasoning semigroup public

module Identity {a : Carrier } where
    id-unique : (∀ b → b ∙ a ≈ b) → a ≈ ε
    id-unique b∙a≈b = trans (sym (identityˡ a) ) (b∙a≈b ε)

    id-comm : a ∙ ε ≈ ε ∙ a
    id-comm = begin
        a ∙ ε ≈⟨ identityʳ a ⟩
        a     ≈⟨ sym (identityˡ a)⟩
        ε ∙ a ∎

    id-comm-sym : ε ∙ a ≈ a ∙ ε
    id-comm-sym = sym id-comm

open Identity public

module IntroElim {a b : Carrier} (a≈ε : a ≈ ε) where
    elimʳ : b ∙ a ≈ b
    elimʳ = begin
         b ∙ a ≈⟨ ∙-congˡ a≈ε ⟩
         b ∙ ε ≈⟨ identityʳ b ⟩
         b     ∎

    elimˡ : a ∙ b ≈ b
    elimˡ = begin
        a ∙ b ≈⟨ ∙-congʳ a≈ε ⟩
        ε ∙ b ≈⟨ identityˡ b ⟩
        b     ∎

    introʳ : a ≈ ε → b ≈ b ∙ a
    introʳ a≈ε = sym elimʳ

    introˡ : a ≈ ε → b ≈ a ∙ b
    introˡ a≈ε = sym elimˡ

    introcenter : ∀ c → b ∙ c ≈ b ∙ (a ∙ c)
    introcenter c = begin
        b ∙ c       ≈⟨ ∙-congˡ  (identityˡ c) ⟨
        b ∙ (ε ∙ c) ≈⟨ ∙-congˡ (∙-congʳ a≈ε) ⟨
        b ∙ (a ∙ c) ∎

open IntroElim public

module Cancellers {a b c : Carrier} (inv : a ∙ c ≈ ε) where

  cancelʳ : (b ∙ a) ∙ c ≈ b
  cancelʳ = begin
    (b ∙ a) ∙ c  ≈⟨ assoc b a c ⟩
    b ∙ (a ∙ c)  ≈⟨ ∙-congˡ inv ⟩
    b ∙ ε        ≈⟨ identityʳ b ⟩
    b            ∎


  cancelˡ : a ∙ (c ∙ b) ≈ b
  cancelˡ = begin
    a ∙ (c ∙ b)  ≈⟨ assoc a c b ⟨
    (a ∙ c) ∙ b  ≈⟨ ∙-congʳ inv ⟩
    ε ∙ b        ≈⟨ identityˡ b ⟩
    b            ∎

  insertˡ : b ≈ a ∙ (c ∙ b)
  insertˡ = sym cancelˡ

  insertʳ : b ≈ (b ∙ a) ∙ c
  insertʳ = sym cancelʳ

  cancelInner : ∀ {g} → (b ∙ a) ∙ (c ∙ g) ≈ b ∙ g
  cancelInner {g = g} = begin
    (b ∙ a) ∙ (c ∙ g)  ≈⟨ assoc (b ∙ a) c g ⟨
    ((b ∙ a) ∙ c) ∙ g  ≈⟨ ∙-congʳ cancelʳ ⟩
    b ∙ g              ∎

  insertInner : ∀ {g} → b ∙ g ≈ (b ∙ a) ∙ (c ∙ g)
  insertInner = sym cancelInner
