------------------------------------------------------------------------
-- The Agda standard library
--
-- Homomorphism proofs for variables and constants over polynomials
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Tactic.RingSolver.Core.Polynomial.Parameters

module Tactic.RingSolver.Core.Polynomial.Homomorphism.Variables
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Product        using (_,_)
open import Data.Vec.Base as Vec     using (Vec)
open import Data.Fin            using (Fin)
open import Data.List.Kleene

open Homomorphism homo

open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Lemmas homo
open import Tactic.RingSolver.Core.Polynomial.Base (Homomorphism.from homo)
open import Tactic.RingSolver.Core.Polynomial.Reasoning (Homomorphism.to homo)
open import Tactic.RingSolver.Core.Polynomial.Semantics homo

open import Algebra.Operations.Ring rawRing

ι-hom : ∀ {n} (i : Fin n) (Ρ : Vec Carrier n) → ⟦ ι i ⟧ Ρ ≈ Vec.lookup Ρ i
ι-hom i Ρ′ = let (ρ , Ρ) = drop-1 (space≤′n i) Ρ′ in begin
  ⟦ (κ Raw.1# Δ 1 ∷↓ []) ⊐↓ space≤′n i ⟧ Ρ′  ≈⟨ ⊐↓-hom (κ Raw.1# Δ 1 ∷↓ []) (space≤′n i) Ρ′ ⟩
  ⅀?⟦ κ Raw.1# Δ 1 ∷↓ [] ⟧ (ρ , Ρ)           ≈⟨ ∷↓-hom-s (κ Raw.1#) 0 [] ρ Ρ  ⟩
  ρ * ⟦ κ Raw.1# ⟧ Ρ                         ≈⟨ *≫ 1-homo ⟩
  ρ * 1#                                     ≈⟨ *-identityʳ ρ ⟩
  ρ                                          ≡⟨ drop-1⇒lookup i Ρ′ ⟩
  Vec.lookup Ρ′ i                            ∎
