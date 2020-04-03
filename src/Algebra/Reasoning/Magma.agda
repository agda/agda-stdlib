------------------------------------------------------------------------
-- The Agda standard library
--
-- Magma reasoning
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles

module Algebra.Reasoning.Magma {m ℓ} (M : Magma m ℓ) where

open import Algebra.Reasoning.Magma.Expr M
open import Algebra.Reasoning.Magma.Expr.Equality M
open import Data.Tree.Binary.Indexed

open Magma M

private
  variable
    s₁ s₂ : 𝕋

infix  4 _IsRelatedTo_
infix  3 _∎
infixr 2 step-≃ step-≃˘
infixr 2 _≃⟨⟩_
infix  1 begin_

------------------------------------------------------------------------
-- Definition of "related to"

-- See Relation.Binary.Reasoning.Base.Partial for explaination

data _IsRelatedTo_ (x : Expr s₁) (y : Expr s₂) : Set ℓ where
  relTo : (x≃y : x ≃ y) → x IsRelatedTo y

------------------------------------------------------------------------
-- Reasoning combinators

-- Beginning of a proof

begin_ : ∀ {x : Expr s₁} {y : Expr s₂} → x IsRelatedTo y → x ≃ y
begin relTo x≃y = x≃y

-- Step with the relation: Applies the given equality to the focus.

step-≃ : ∀ (x : Expr s₁) {g : Carrier} {y : Expr s₂} →
           replace-at-focus x g IsRelatedTo y →
           focus x ≈ g →
           x IsRelatedTo y
step-≃ x (relTo rest) fx≈g = relTo (trans (cong-expr x fx≈g) rest)

-- Step using a symmetric equality

step-≃˘ : ∀ (x : Expr s₁) {g : Carrier} {y : Expr s₂} →
            replace-at-focus x g IsRelatedTo y →
            g ≈ focus x →
            x IsRelatedTo y
step-≃˘ x (relTo rest) g≈fx = relTo (trans (cong-expr x (sym g≈fx)) rest)

-- Step with a trivial equality

_≃⟨⟩_ : ∀ (x : Expr s₁) {y : Expr s₂} →
          x IsRelatedTo y →
          x IsRelatedTo y
_ ≃⟨⟩ x≃y = x≃y

-- Termination step

_∎ : ∀ (x : Expr s₁) → x IsRelatedTo x
_ ∎ = relTo refl

-- Syntax declarations

syntax step-≃  x fx≈g rest = x ≃⌊ fx≈g ⌋ rest
syntax step-≃˘ x g≈fx rest = x ≃⌊ g≈fx ⌋ rest
