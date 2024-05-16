------------------------------------------------------------------------
-- The Agda standard library
--
-- Application of substitutions to lists, along with various lemmas
------------------------------------------------------------------------

-- This module illustrates how Data.Fin.Substitution.Lemmas.AppLemmas
-- can be used.

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin.Substitution.Lemmas using (Lemmas₄; AppLemmas)
open import Data.Nat.Base using (ℕ)

module Data.Fin.Substitution.List {ℓ} {T : ℕ → Set ℓ} (lemmas₄ : Lemmas₄ T) where

open import Data.List.Base using (List; map)
open import Data.List.Properties using (map-id; map-cong; map-∘)
open import Data.Fin.Substitution using (Sub)
import Function.Base as Fun
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

private
  variable
    m n : ℕ

  ListT : ℕ → Set ℓ
  ListT = List Fun.∘ T

  open module L = Lemmas₄ lemmas₄ using (_/_; id; _⊙_)

------------------------------------------------------------------------
-- Listwise application of a substitution, plus lemmas about it

infixl 8 _//_

_//_ : ListT m → Sub T m n → ListT n
ts // ρ = map (λ σ → σ / ρ) ts

appLemmas : AppLemmas ListT T
appLemmas = record
  { application = record { _/_ = _//_ }
  ; lemmas₄     = lemmas₄
  ; id-vanishes = λ ts → begin
      ts // id       ≡⟨ map-cong L.id-vanishes ts ⟩
      map Fun.id ts  ≡⟨ map-id ts ⟩
      ts             ∎
  ; /-⊙ = λ {_ _ _ ρ₁ ρ₂} ts → begin
      ts // ρ₁ ⊙ ρ₂               ≡⟨ map-cong L./-⊙ ts ⟩
      map (λ σ → σ / ρ₁ / ρ₂) ts  ≡⟨ map-∘ ts ⟩
      ts // ρ₁ // ρ₂              ∎
  } where open ≡-Reasoning

open AppLemmas appLemmas public
  hiding (_/_) renaming (_/✶_ to _//✶_)
