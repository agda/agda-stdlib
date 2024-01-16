------------------------------------------------------------------------
-- The Agda standard library
--
-- Induction related to mod fin
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Mod.Induction where

open import Function.Base using (id; _∘_; _$_)
open import Data.Fin.Base hiding (_+_; _-_)
open import Data.Fin.Induction using (<-weakInduction-startingFrom; <-weakInduction)
open import Data.Fin.Properties
open import Data.Fin.Mod
open import Data.Fin.Mod.Properties
open import Data.Nat.Base as ℕ using (ℕ; z≤n)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality using (subst)

private variable
  m n : ℕ

module _ {ℓ} (P : Pred (Fin (ℕ.suc n)) ℓ)
  (Pᵢ⇒Pᵢ₊₁ : ∀ {i} → P i → P (sucMod i)) where

  module _ {k} (Pₖ : P k) where

    induction-≥ : ∀ {i} → i ≥ k → P i
    induction-≥ = <-weakInduction-startingFrom P Pₖ Pᵢ⇒Pᵢ₊₁′
      where
      PInj : ∀ {i} → P (sucMod (inject₁ i)) → P (suc i)
      PInj {i} rewrite sucMod-inject₁ i = id

      Pᵢ⇒Pᵢ₊₁′ : ∀ i → P (inject₁ i) → P (suc i)
      Pᵢ⇒Pᵢ₊₁′ _ = PInj ∘ Pᵢ⇒Pᵢ₊₁

    induction-0 : P zero
    induction-0 = subst P (sucMod-fromℕ _) $ Pᵢ⇒Pᵢ₊₁ $ induction-≥ $ ≤fromℕ _


  induction : ∀ {k} (Pₖ : P k) → ∀ i → P i
  induction Pₖ i = induction-≥ (induction-0 Pₖ) z≤n
