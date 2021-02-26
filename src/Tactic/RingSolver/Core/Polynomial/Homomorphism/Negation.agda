------------------------------------------------------------------------
-- The Agda standard library
--
-- Homomorphism proofs for negation over polynomials
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Tactic.RingSolver.Core.Polynomial.Parameters

module Tactic.RingSolver.Core.Polynomial.Homomorphism.Negation
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Product          using (_,_)
open import Data.Vec              using (Vec)
open import Data.Nat              using (_<′_)
open import Data.Nat.Induction

open import Function

open Homomorphism homo
open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Lemmas homo
open import Tactic.RingSolver.Core.Polynomial.Reasoning to
open import Tactic.RingSolver.Core.Polynomial.Base from
open import Tactic.RingSolver.Core.Polynomial.Semantics homo

⊟-step-hom : ∀ {n} (a : Acc _<′_ n) → (xs : Poly n) → ∀ ρ → ⟦ ⊟-step a xs ⟧ ρ ≈ - (⟦ xs ⟧ ρ)
⊟-step-hom (acc _ ) (Κ x  ⊐ i≤n) ρ = neg-homo x
⊟-step-hom (acc wf) (⅀ xs ⊐ i≤n) ρ′ =
  let (ρ , ρs) = drop-1 i≤n ρ′
      neg-zero =
        begin
          0#
        ≈⟨ sym (zeroʳ _) ⟩
          - 0# * 0#
        ≈⟨ sym (neg-distribˡ-* 0# 0#) ⟩
          - (0# * 0#)
        ≈⟨ neg-cong (zeroˡ 0#) ⟩
          - 0#
        ∎
  in
  begin
    ⟦ poly-map (⊟-step (wf _ i≤n)) xs ⊐↓ i≤n ⟧ ρ′
  ≈⟨ ⊐↓-hom (poly-map (⊟-step (wf _ i≤n)) xs) i≤n ρ′ ⟩
    ⅀?⟦ poly-map (⊟-step  (wf _ i≤n)) xs ⟧ (ρ , ρs)
  ≈⟨ poly-mapR ρ ρs (⊟-step (wf _ i≤n)) -_ (neg-cong) (λ x y → *-comm x (- y) ⟨ trans ⟩ sym (neg-distribˡ-* y x) ⟨ trans ⟩ neg-cong (*-comm _ _)) (λ x y → neg-distrib-+ x y) (flip (⊟-step-hom (wf _ i≤n)) ρs) (sym neg-zero ) xs ⟩
    - ⅀⟦ xs ⟧ (ρ , ρs)
  ∎

⊟-hom : ∀ {n}
      → (xs : Poly n)
      → (Ρ : Vec Carrier n)
      → ⟦ ⊟ xs ⟧ Ρ ≈ - ⟦ xs ⟧ Ρ
⊟-hom = ⊟-step-hom (<′-wellFounded _)
