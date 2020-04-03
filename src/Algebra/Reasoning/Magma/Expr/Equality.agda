------------------------------------------------------------------------
-- The Agda standard library
--
-- Setoid for magma reasoning
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles

module Algebra.Reasoning.Magma.Expr.Equality {c ℓ} (M : Magma c ℓ) where

open Magma M

open import Algebra.Reasoning.Magma.Expr M
open import Relation.Binary using (Setoid)
open import Data.Product
open import Data.Tree.Binary.Indexed

private
  variable
    s s₁ s₂ s₃ : 𝕋
    e : Expr s
    e₁ : Expr s₁
    e₂ : Expr s₂
    e₃ : Expr s₃


_≃_ : Expr s₁ → Expr s₂ → Set ℓ
e₁ ≃ e₂ = eval e₁ ≈ eval e₂

≃-refl : e ≃ e
≃-refl = refl

≃-sym : e₁ ≃ e₂ → e₂ ≃ e₁
≃-sym = sym

≃-trans : e₁ ≃ e₂ → e₂ ≃ e₃ → e₁ ≃ e₃
≃-trans = trans

cong-expr : ∀ {s} →
            (e : Expr s) →
            {h : Carrier} →
            focus e ≈ h →
            e ≃ replace-at-focus e h
cong-expr (leaf x , here-l) eq = eq
cong-expr (node l m r , il-l i) eq = ∙-congʳ (cong-expr (l , i) eq)
cong-expr (node l m r , il-r i) eq = ∙-congˡ (cong-expr (r , i) eq)
