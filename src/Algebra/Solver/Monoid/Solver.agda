------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for equations over monoids
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)
import Algebra.Solver.Monoid.Expression as Expression

module Algebra.Solver.Monoid.Solver {a c ℓ} (M : Monoid c ℓ)
  (open Monoid M using (rawMonoid; setoid; _≈_))
  (open Expression rawMonoid using (Expr; Env; var; ⟦_⟧; NormalAPI))
  (N : NormalAPI a) where

open import Data.Maybe.Base as Maybe
  using (Maybe; From-just; from-just)
open import Data.Nat.Base using (ℕ)
open import Function.Base using (_∘_; _$_)
open import Relation.Binary.Consequences using (dec⇒weaklyDec)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong)
import Relation.Binary.Reflection as Reflection

open NormalAPI N

private
  variable
    n : ℕ
  module
    R = Reflection setoid var ⟦_⟧ (⟦_⟧⇓ ∘ normalise) correct


------------------------------------------------------------------------
-- Proof procedures

-- Re-export the existing solver machinery from `Reflection`

open R public
  using (solve; _⊜_)

-- We can also give a sound, but not necessarily complete, procedure
-- for determining if two expressions have the same semantics.

prove′ : ∀ e₁ e₂ → Maybe ((ρ : Env n) → ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ)
prove′ e₁ e₂ = Maybe.map lemma $ dec⇒weaklyDec _≟_ (normalise e₁) (normalise e₂)
  where
  open import Relation.Binary.Reasoning.Setoid setoid
  lemma : normalise e₁ ≡ normalise e₂ → ∀ ρ → ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ
  lemma eq ρ = R.prove ρ e₁ e₂ $ begin
    ⟦ normalise e₁ ⟧⇓ ρ  ≡⟨ cong (λ e → ⟦ e ⟧⇓ ρ) eq ⟩
    ⟦ normalise e₂ ⟧⇓ ρ  ∎

-- This procedure can then be combined with from-just.

prove : ∀ n (e₁ e₂ : Expr n) → From-just (prove′ e₁ e₂)
prove _ e₁ e₂ = from-just $ prove′ e₁ e₂
