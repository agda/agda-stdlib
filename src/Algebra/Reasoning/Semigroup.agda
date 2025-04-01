------------------------------------------------------------------------
-- The Agda standard library
--
-- Equational reasoning for semigroups
-- (Utilities for associativity reasoning, pulling and pushing operations)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra using (Semigroup)

module Algebra.Reasoning.Semigroup {o ℓ} (S : Semigroup o ℓ) where

open Semigroup S
    using (Carrier; _∙_; _≈_; setoid; trans ; refl; sym; assoc; ∙-cong)
open import Relation.Binary.Reasoning.Setoid setoid

private
 variable
    a b c d e x y z : Carrier

module Assoc4  {a b c d : Carrier} where
    {-
  Explanation of naming scheme:

  Each successive association is given a Greek letter, from 'α' associated all
  the way to the left, to 'ε' associated all the way to the right. Then,
  'assoc²XY' is the proof that X is equal to Y. Explicitly:

  α = ((a ∙ b) ∙ c) ∙ d
  β = (a ∙ (b ∙ c)) ∙ d
  γ = (a ∙ b) ∙ (c ∙ d)
  δ = a ∙ ((b ∙ c) ∙ d)
  ε = a ∙ (b ∙ (c ∙ d))

  Only reassociations that need two assoc steps are defined here.
  -}
  assoc²αδ : ((a ∙ b) ∙ c) ∙ d ≈ a ∙ ((b ∙ c) ∙ d)
  assoc²αδ = trans (∙-cong (assoc a b c) refl) (assoc a (b ∙ c) d)

  assoc²αε : ((a ∙ b) ∙ c) ∙ d ≈ a ∙ (b ∙ (c ∙ d))
  assoc²αε = trans (assoc (a ∙ b) c d) (assoc a b (c ∙ d))

  assoc²βγ : (a ∙ (b ∙ c)) ∙ d ≈ (a ∙ b) ∙ (c ∙ d)
  assoc²βγ = trans (sym (∙-cong (assoc a b c) refl)) (assoc (a ∙ b) c d)

  assoc²βε : (a ∙ (b ∙ c)) ∙ d ≈ a ∙ (b ∙ (c ∙ d))
  assoc²βε = trans (assoc a (b ∙ c) d) (∙-cong refl (assoc b c d))

  assoc²γβ : (a ∙ b) ∙ (c ∙ d) ≈ (a ∙ (b ∙ c)) ∙ d
  assoc²γβ = trans (sym (assoc (a ∙ b) c d)) (∙-cong (assoc a b c) refl)

  assoc²γδ : (a ∙ b) ∙ (c ∙ d) ≈ a ∙ ((b ∙ c) ∙ d)
  assoc²γδ = begin
    (a ∙ b) ∙ (c ∙ d) ≈⟨ assoc a b (c ∙ d) ⟩
    a ∙ (b ∙ (c ∙ d)) ≈⟨ ∙-cong refl (sym (assoc b c d)) ⟩
    a ∙ ((b ∙ c) ∙ d) ∎

  assoc²δα : a ∙ ((b ∙ c) ∙ d) ≈ ((a ∙ b) ∙ c) ∙ d
  assoc²δα = sym (trans (∙-cong (assoc a b c) refl) (assoc a (b ∙ c) d))

  assoc²δγ : a ∙ ((b ∙ c) ∙ d) ≈ (a ∙ b) ∙ (c ∙ d)
  assoc²δγ = begin
    a ∙ ((b ∙ c) ∙ d) ≈⟨ ∙-cong refl (assoc b c d) ⟩
    a ∙ (b ∙ (c ∙ d)) ≈⟨ sym (assoc a b (c ∙ d)) ⟩
    (a ∙ b) ∙ (c ∙ d) ∎

  assoc²εα : a ∙ (b ∙ (c ∙ d)) ≈ ((a ∙ b) ∙ c) ∙ d
  assoc²εα = sym (trans (assoc (a ∙ b) c d) (assoc a b (c ∙ d)))

  assoc²εβ : a ∙ (b ∙ (c ∙ d)) ≈ (a ∙ (b ∙ c)) ∙ d
  assoc²εβ = sym (trans (assoc a (b ∙ c) d) (∙-cong refl (assoc b c d)))

open Assoc4 public

module Pulls (ab≡c : a ∙ b ≈ c) where
    pullʳ : ∀ {x} → (x ∙ a) ∙ b ≈ x ∙ c
    pullʳ {x = x} = begin
        (x ∙ a) ∙ b ≈⟨ assoc x a b ⟩
        x ∙ (a ∙ b) ≈⟨ ∙-cong refl ab≡c ⟩
        x ∙ c       ∎

    pullˡ : ∀ {x} → a ∙ (b ∙ x) ≈ c ∙ x
    pullˡ {x = x} = begin
        a ∙ (b ∙ x) ≈⟨ sym (assoc a b x) ⟩
        (a ∙ b) ∙ x ≈⟨ ∙-cong ab≡c refl ⟩
        c ∙ x       ∎

    pull-first : ∀ {x y} → a ∙ ((b ∙ x) ∙ y) ≈ c ∙ (x ∙ y)
    pull-first {x = x} {y = y} = begin
      a ∙ ((b ∙ x) ∙ y) ≈⟨ ∙-cong refl (assoc b x y) ⟩
      a ∙ (b ∙ (x ∙ y)) ≈⟨ pullˡ ⟩
      c ∙ (x ∙ y)       ∎

    pull-center : ∀ {x y} → x ∙ (a ∙ (b ∙ y)) ≈ x ∙ (c ∙ y)
    pull-center {x = x} {y = y} = ∙-cong refl (pullˡ)

    -- could be called pull₃ʳ
    pull-last : ∀ {x y} → (x ∙ (y ∙ a)) ∙ b ≈ x ∙ (y ∙ c)
    pull-last {x = x} {y = y} = begin
      (x ∙ (y ∙ a)) ∙ b ≈⟨ assoc x (y ∙ a) b ⟩
      x ∙ ((y ∙ a) ∙ b) ≈⟨ ∙-cong refl (pullʳ {x = y}) ⟩
      x ∙ (y ∙ c)       ∎

open Pulls public

module Pushes (ab≡c : a ∙ b ≈ c) where
    pushʳ : x ∙ c ≈ (x ∙ a) ∙ b
    pushʳ {x = x} = begin
        x ∙ c       ≈⟨ sym (∙-cong refl ab≡c) ⟩
        x ∙ (a ∙ b) ≈⟨ sym (assoc x a b) ⟩
        (x ∙ a) ∙ b ∎

    pushˡ : c ∙ x ≈ a ∙ (b ∙ x)
    pushˡ {x = x} = begin
        c ∙ x       ≈⟨ sym (∙-cong ab≡c refl) ⟩
        (a ∙ b) ∙ x ≈⟨ assoc a b x ⟩
        a ∙ (b ∙ x) ∎
open Pushes public

-- operate in the 'center' instead (like pull/push)
center : a ∙ b ≈ c → (d ∙ a) ∙ (b ∙ e) ≈ d ∙ (c ∙ e)
center eq = pullʳ (pullˡ eq)

-- operate on the left part, then the right part
center⁻¹ : a ∙ b ≈ c → x ∙ y ≈ z →  a ∙ ((b ∙ x) ∙ y) ≈ c ∙ z
center⁻¹ {a = a} {b = b} {c = c} {x = x} {y = y} {z = z} eq eq′ = begin
  a ∙ ((b ∙ x) ∙ y) ≈⟨ ∙-cong refl (pullʳ eq′) ⟩
  a ∙ (b ∙ z)       ≈⟨ pullˡ eq ⟩
  c ∙ z             ∎

push-center : a ∙ b ≈ c → x ∙ (c ∙ y) ≈ x ∙ (a ∙ (b ∙ y))
push-center eq = sym (pull-center eq)

module Extends {a b c d : Carrier} (s : a ∙ b ≈ c ∙ d) where
  -- rewrite (x ∙ a) ∙ b to (x ∙ c) ∙ d
  extendˡ : (x ∙ a) ∙ b ≈ (x ∙ c) ∙ d
  extendˡ {x = x} = begin
    (x ∙ a) ∙ b ≈⟨ pullʳ s ⟩
    x ∙ (c ∙ d) ≈⟨ sym (assoc x c d) ⟩
    (x ∙ c) ∙ d ∎

  -- rewrite a ∙ (b ∙ x) to c ∙ (d ∙ x)
  extendʳ : a ∙ (b ∙ x) ≈ c ∙ (d ∙ x)
  extendʳ {x = x} = begin
    a ∙ (b ∙ x) ≈⟨ pullˡ s ⟩
    (c ∙ d) ∙ x ≈⟨ assoc c d x ⟩
    c ∙ (d ∙ x) ∎

  -- rewrite (x ∙ a) ∙ (b ∙ y) to (x ∙ c) ∙ (d ∙ y)
  extend² : ∀ x y → (x ∙ a) ∙ (b ∙ y) ≈ (x ∙ c) ∙ (d ∙ y)
  extend² x y = begin
    (x ∙ a) ∙ (b ∙ y) ≈⟨ pullʳ (extendʳ {x = y}) ⟩
    x ∙ (c ∙ (d ∙ y)) ≈⟨ sym (assoc x c (d ∙ y)) ⟩
    (x ∙ c) ∙ (d ∙ y) ∎

open Extends public