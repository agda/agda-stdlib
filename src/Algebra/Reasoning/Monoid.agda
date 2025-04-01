{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra using (Monoid)

module Algebra.Reasoning.Monoid {o ℓ} (M : Monoid o ℓ) where

open Monoid M
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Reasoning.SemiGroup semigroup public


module Identity {a : Carrier } where
    id-unique : (∀ b → b ∙ a ≈ b) → a ≈ ε
    id-unique b∙a≈b = begin
        a     ≈⟨ sym (identityˡ a) ⟩
        ε ∙ a ≈⟨ b∙a≈b ε ⟩
        ε     ∎

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
         b ∙ a ≈⟨ ∙-cong refl a≈ε ⟩
         b ∙ ε ≈⟨ identityʳ b ⟩
         b     ∎

    elimˡ : a ∙ b ≈ b
    elimˡ = begin
        a ∙ b ≈⟨ ∙-cong a≈ε refl ⟩
        ε ∙ b ≈⟨ identityˡ b ⟩
        b     ∎

    introʳ : a ≈ ε → b ≈ b ∙ a
    introʳ a≈ε = sym elimʳ

    introˡ : a ≈ ε → b ≈ a ∙ b
    introˡ a≈ε = sym elimˡ

    introcenter : ∀ c → b ∙ c ≈ b ∙ (a ∙ c)
    introcenter c = begin
        b ∙ c       ≈⟨ sym (∙-cong refl (identityˡ c)) ⟩
        b ∙ (ε ∙ c) ≈⟨ sym (∙-cong refl (∙-cong a≈ε refl)) ⟩
        b ∙ (a ∙ c) ∎

open IntroElim public

module Cancellers {a b c : Carrier} (inv : a ∙ c ≈ ε) where

  cancelʳ : (b ∙ a) ∙ c ≈ b
  cancelʳ = begin
    (b ∙ a) ∙ c  ≈⟨ assoc b a c ⟩
    b ∙ (a ∙ c)  ≈⟨ ∙-cong refl inv ⟩
    b ∙ ε        ≈⟨ identityʳ b ⟩
    b            ∎


  cancelˡ : a ∙ (c ∙ b) ≈ b
  cancelˡ = begin
    a ∙ (c ∙ b)  ≈⟨ sym (assoc a c b) ⟩
    (a ∙ c) ∙ b  ≈⟨ ∙-cong inv refl ⟩
    ε ∙ b        ≈⟨ identityˡ b ⟩
    b            ∎

  insertˡ : b ≈ a ∙ (c ∙ b)
  insertˡ = sym cancelˡ

  insertʳ : b ≈ (b ∙ a) ∙ c
  insertʳ = sym cancelʳ

  cancelInner : ∀ {g} → (b ∙ a) ∙ (c ∙ g) ≈ b ∙ g
  cancelInner {g = g} = begin
    (b ∙ a) ∙ (c ∙ g)  ≈⟨ sym (assoc (b ∙ a) c g) ⟩
    ((b ∙ a) ∙ c) ∙ g  ≈⟨ ∙-cong cancelʳ refl ⟩
    b ∙ g              ∎

  insertInner : ∀ {g} → b ∙ g ≈ (b ∙ a) ∙ (c ∙ g)
  insertInner = sym cancelInner
