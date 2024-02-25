------------------------------------------------------------------------
-- The Agda standard library
--
-- An example of how Data.Fin.Substitution can be used: a definition
-- of substitution for the untyped λ-calculus, along with some lemmas
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module README.Data.Fin.Substitution.UntypedLambda where

open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat.Base hiding (_/_)
open import Data.Fin.Base using (Fin)
open import Data.Vec.Base
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

open ≡-Reasoning

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- A representation of the untyped λ-calculus. Uses de Bruijn indices.

infixl 9 _·_

data Lam (n : ℕ) : Set where
  var : (x : Fin n) → Lam n
  ƛ   : (t : Lam (suc n)) → Lam n
  _·_ : (t₁ t₂ : Lam n) → Lam n

------------------------------------------------------------------------
-- Code for applying substitutions.

module LamApp {ℓ} {T : ℕ → Set ℓ} (l : Lift T Lam) where
  open Lift l hiding (var)

  -- Applies a substitution to a term.

  infixl 8 _/_

  _/_ : Lam m → Sub T m n → Lam n
  var x   / ρ = lift (lookup ρ x)
  ƛ t     / ρ = ƛ (t / ρ ↑)
  t₁ · t₂ / ρ = (t₁ / ρ) · (t₂ / ρ)

  open Application (record { _/_ = _/_ }) using (_/✶_)

  -- Some lemmas about _/_.

  ƛ-/✶-↑✶ : ∀ k {t} (ρs : Subs T m n) →
            ƛ t /✶ ρs ↑✶ k ≡ ƛ (t /✶ ρs ↑✶ suc k)
  ƛ-/✶-↑✶ k ε        = refl
  ƛ-/✶-↑✶ k (ρ ◅ ρs) = cong (_/ _) (ƛ-/✶-↑✶ k ρs)

  ·-/✶-↑✶ : ∀ k {t₁ t₂} (ρs : Subs T m n) →
            t₁ · t₂ /✶ ρs ↑✶ k ≡ (t₁ /✶ ρs ↑✶ k) · (t₂ /✶ ρs ↑✶ k)
  ·-/✶-↑✶ k ε        = refl
  ·-/✶-↑✶ k (ρ ◅ ρs) = cong (_/ _) (·-/✶-↑✶ k ρs)

lamSubst : TermSubst Lam
lamSubst = record { var = var; app = LamApp._/_ }

open TermSubst lamSubst hiding (var)

------------------------------------------------------------------------
-- Substitution lemmas.

lamLemmas : TermLemmas Lam
lamLemmas = record
  { termSubst = lamSubst
  ; app-var   = refl
  ; /✶-↑✶     = Lemma./✶-↑✶
  }
  where
  module Lemma {T₁ T₂} {lift₁ : Lift T₁ Lam} {lift₂ : Lift T₂ Lam} where

    open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
    open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

    /✶-↑✶ : (ρs₁ : Subs T₁ m n) (ρs₂ : Subs T₂ m n) →
            (∀ k x → var x /✶₁ ρs₁ ↑✶₁ k ≡ var x /✶₂ ρs₂ ↑✶₂ k) →
             ∀ k t → t     /✶₁ ρs₁ ↑✶₁ k ≡ t     /✶₂ ρs₂ ↑✶₂ k
    /✶-↑✶ ρs₁ ρs₂ hyp k (var x) = hyp k x
    /✶-↑✶ ρs₁ ρs₂ hyp k (ƛ t)   = begin
      ƛ t /✶₁ ρs₁ ↑✶₁ k        ≡⟨ LamApp.ƛ-/✶-↑✶ _ k ρs₁ ⟩
      ƛ (t /✶₁ ρs₁ ↑✶₁ suc k)  ≡⟨ cong ƛ (/✶-↑✶ ρs₁ ρs₂ hyp (suc k) t) ⟩
      ƛ (t /✶₂ ρs₂ ↑✶₂ suc k)  ≡⟨ sym (LamApp.ƛ-/✶-↑✶ _ k ρs₂) ⟩
      ƛ t /✶₂ ρs₂ ↑✶₂ k        ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k (t₁ · t₂) = begin
      t₁ · t₂ /✶₁ ρs₁ ↑✶₁ k                    ≡⟨ LamApp.·-/✶-↑✶ _ k ρs₁ ⟩
      (t₁ /✶₁ ρs₁ ↑✶₁ k) · (t₂ /✶₁ ρs₁ ↑✶₁ k)  ≡⟨ cong₂ _·_ (/✶-↑✶ ρs₁ ρs₂ hyp k t₁)
                                                            (/✶-↑✶ ρs₁ ρs₂ hyp k t₂) ⟩
      (t₁ /✶₂ ρs₂ ↑✶₂ k) · (t₂ /✶₂ ρs₂ ↑✶₂ k)  ≡⟨ sym (LamApp.·-/✶-↑✶ _ k ρs₂) ⟩
      t₁ · t₂ /✶₂ ρs₂ ↑✶₂ k                    ∎

open TermLemmas lamLemmas public hiding (var)
