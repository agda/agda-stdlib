------------------------------------------------------------------------
-- The Agda standard library
--
-- Core lemmas for division and modulus operations
------------------------------------------------------------------------

module Data.Nat.DivMod.Core where

open import Agda.Builtin.Nat using ()
  renaming (div-helper to divₕ; mod-helper to modₕ)

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

open SemiringSolver
open ≡-Reasoning

-------------------------------------------------------------------------
-- mod lemmas

a[modₕ]1≡0 : ∀ a → modₕ 0 0 a 0 ≡ 0
a[modₕ]1≡0 zero    = refl
a[modₕ]1≡0 (suc a) = a[modₕ]1≡0 a

mod-lemma : ∀ acc d n → modₕ acc (acc + n) d n ≤ acc + n
mod-lemma acc zero    n       = m≤m+n acc n
mod-lemma acc (suc d) zero    = mod-lemma zero d (acc + 0)
mod-lemma acc (suc d) (suc n)
          rewrite +-suc acc n = mod-lemma (suc acc) d n

-------------------------------------------------------------------------
-- division lemmas

-- The quotient and remainder are related to the dividend and
-- divisor in the right way.

division-lemma : ∀ accᵐ accᵈ d n →
    accᵐ + accᵈ * suc (accᵐ + n) + d ≡
    modₕ accᵐ (accᵐ + n) d n + divₕ accᵈ (accᵐ + n) d n * suc (accᵐ + n)
division-lemma accᵐ accᵈ zero    n    = +-identityʳ _
division-lemma accᵐ accᵈ (suc d) zero rewrite +-identityʳ accᵐ = begin
  accᵐ + accᵈ * suc accᵐ + suc d          ≡⟨ +-suc _ d ⟩
  suc accᵈ * suc accᵐ + d                 ≡⟨ division-lemma zero (suc accᵈ) d accᵐ ⟩
  modₕ 0          accᵐ d accᵐ +
  divₕ (suc accᵈ) accᵐ d accᵐ * suc accᵐ  ≡⟨⟩
  modₕ accᵐ accᵐ (suc d) 0 +
  divₕ accᵈ accᵐ (suc d) 0 * suc accᵐ      ∎
  where open ≡-Reasoning
division-lemma accᵐ accᵈ (suc d) (suc n) rewrite +-suc accᵐ n = begin
  accᵐ + accᵈ * (2 + accᵐ + n) + suc d             ≡⟨ +-suc _ d ⟩
  suc (accᵐ + accᵈ * (2 + accᵐ + n) + d)           ≡⟨ division-lemma (suc accᵐ) accᵈ d n ⟩
  modₕ (suc accᵐ) (suc (accᵐ + n)) d n +
  divₕ accᵈ (suc (accᵐ + n)) d n * (2 + accᵐ + n)  ∎
  where
  open ≡-Reasoning
