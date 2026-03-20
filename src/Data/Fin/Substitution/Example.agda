------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please see
-- `README.Data.Nat.Fin.Substitution.UntypedLambda` instead.
--
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Substitution.Example where

{-# WARNING_ON_IMPORT
"Data.Fin.Substitution.Example was deprecated in v2.0.
Please see README.Data.Fin.Substitution.UntypedLambda instead."
#-}

open import Data.Fin.Substitution using (Lift; Sub; Subs; Application; TermSubst)
open import Data.Fin.Substitution.Lemmas using (TermLemmas)
open import Data.Nat.Base hiding (_/_)
open import Data.Fin.Base using (Fin)
open import Data.Vec.Base using (Vec; _∷_; []; lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

-- A representation of the untyped λ-calculus. Uses de Bruijn indices.

infixl 9 _·_

data Tm (n : ℕ) : Set where
  var : (x : Fin n) → Tm n
  ƛ   : (t : Tm (suc n)) → Tm n
  _·_ : (t₁ t₂ : Tm n) → Tm n

-- Code for applying substitutions.

module TmApp {ℓ} {T : ℕ → Set ℓ} (l : Lift T Tm) where
  open Lift l hiding (var)

  -- Applies a substitution to a term.

  infix 8 _/_

  _/_ : ∀ {m n} → Tm m → Sub T m n → Tm n
  var x   / ρ = lift (lookup ρ x)
  ƛ t     / ρ = ƛ (t / ρ ↑)
  t₁ · t₂ / ρ = (t₁ / ρ) · (t₂ / ρ)

  open Application (record { _/_ = _/_ }) using (_/✶_)

  -- Some lemmas about _/_.

  ƛ-/✶-↑✶ : ∀ k {m n t} (ρs : Subs T m n) →
            ƛ t /✶ ρs ↑✶ k ≡ ƛ (t /✶ ρs ↑✶ suc k)
  ƛ-/✶-↑✶ k ε        = refl
  ƛ-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (ƛ-/✶-↑✶ k ρs) refl

  ·-/✶-↑✶ : ∀ k {m n t₁ t₂} (ρs : Subs T m n) →
            t₁ · t₂ /✶ ρs ↑✶ k ≡ (t₁ /✶ ρs ↑✶ k) · (t₂ /✶ ρs ↑✶ k)
  ·-/✶-↑✶ k ε        = refl
  ·-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (·-/✶-↑✶ k ρs) refl

tmSubst : TermSubst Tm
tmSubst = record { var = var; app = TmApp._/_ }

open TermSubst tmSubst hiding (var)

-- Substitution lemmas.

tmLemmas : TermLemmas Tm
tmLemmas = record
  { termSubst = tmSubst
  ; app-var   = refl
  ; /✶-↑✶     = Lemma./✶-↑✶
  }
  where
  module Lemma {T₁ T₂} {lift₁ : Lift T₁ Tm} {lift₂ : Lift T₂ Tm} where

    open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
    open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

    /✶-↑✶ : ∀ {m n} (ρs₁ : Subs T₁ m n) (ρs₂ : Subs T₂ m n) →
            (∀ k x → var x /✶₁ ρs₁ ↑✶₁ k ≡ var x /✶₂ ρs₂ ↑✶₂ k) →
             ∀ k t → t     /✶₁ ρs₁ ↑✶₁ k ≡ t     /✶₂ ρs₂ ↑✶₂ k
    /✶-↑✶ ρs₁ ρs₂ hyp k (var x) = hyp k x
    /✶-↑✶ ρs₁ ρs₂ hyp k (ƛ t)   = begin
      ƛ t /✶₁ ρs₁ ↑✶₁ k        ≡⟨ TmApp.ƛ-/✶-↑✶ _ k ρs₁ ⟩
      ƛ (t /✶₁ ρs₁ ↑✶₁ suc k)  ≡⟨ cong ƛ (/✶-↑✶ ρs₁ ρs₂ hyp (suc k) t) ⟩
      ƛ (t /✶₂ ρs₂ ↑✶₂ suc k)  ≡⟨ sym (TmApp.ƛ-/✶-↑✶ _ k ρs₂) ⟩
      ƛ t /✶₂ ρs₂ ↑✶₂ k        ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k (t₁ · t₂) = begin
      t₁ · t₂ /✶₁ ρs₁ ↑✶₁ k                    ≡⟨ TmApp.·-/✶-↑✶ _ k ρs₁ ⟩
      (t₁ /✶₁ ρs₁ ↑✶₁ k) · (t₂ /✶₁ ρs₁ ↑✶₁ k)  ≡⟨ cong₂ _·_ (/✶-↑✶ ρs₁ ρs₂ hyp k t₁)
                                                            (/✶-↑✶ ρs₁ ρs₂ hyp k t₂) ⟩
      (t₁ /✶₂ ρs₂ ↑✶₂ k) · (t₂ /✶₂ ρs₂ ↑✶₂ k)  ≡⟨ sym (TmApp.·-/✶-↑✶ _ k ρs₂) ⟩
      t₁ · t₂ /✶₂ ρs₂ ↑✶₂ k                    ∎

open TermLemmas tmLemmas public hiding (var)
