------------------------------------------------------------------------
-- The Agda standard library
--
-- Homomorphism proofs for negation over polynomials
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Tactic.RingSolver.Core.Polynomial.Parameters

module Tactic.RingSolver.Core.Polynomial.Homomorphism.Negation
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Vec.Base         using (Vec)
open import Data.Product.Base     using (_,_)
open import Data.Nat.Base         using (_<′_)
open import Data.Nat.Induction

open import Function.Base using (_⟨_⟩_; flip)

open Homomorphism homo
open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Lemmas homo
open import Tactic.RingSolver.Core.Polynomial.Reasoning to
open import Tactic.RingSolver.Core.Polynomial.Base from
open import Tactic.RingSolver.Core.Polynomial.Semantics homo

⊟-step-hom : ∀ {n} (a : Acc _<′_ n) → (xs : Poly n) → ∀ ρ → ⟦ ⊟-step a xs ⟧ ρ ≈ - (⟦ xs ⟧ ρ)
⊟-step-hom (acc _ ) (Κ x  ⊐ i≤n) ρ = -‿homo x
⊟-step-hom (acc wf) (⅀ xs ⊐ i≤n) ρ′ =
  let (ρ , ρs) = drop-1 i≤n ρ′
      neg-zero =
        begin
          0#
        ≈⟨ sym (zeroʳ _) ⟩
          - 0# * 0#
        ≈⟨ -‿*-distribˡ 0# 0# ⟩
          - (0# * 0#)
        ≈⟨ -‿cong (zeroˡ 0#) ⟩
          - 0#
        ∎
  in
  begin
    ⟦ poly-map (⊟-step (wf i≤n)) xs ⊐↓ i≤n ⟧ ρ′
  ≈⟨ ⊐↓-hom (poly-map (⊟-step (wf i≤n)) xs) i≤n ρ′ ⟩
    ⅀?⟦ poly-map (⊟-step  (wf i≤n)) xs ⟧ (ρ , ρs)
  ≈⟨ poly-mapR ρ ρs (⊟-step (wf i≤n)) -_ (-‿cong) (λ x y → *-comm x (- y) ⟨ trans ⟩ -‿*-distribˡ y x ⟨ trans ⟩ -‿cong (*-comm _ _)) (λ x y → sym (-‿+-comm x y)) (flip (⊟-step-hom (wf i≤n)) ρs) (sym neg-zero ) xs ⟩
    - ⅀⟦ xs ⟧ (ρ , ρs)
  ∎

⊟-hom : ∀ {n}
      → (xs : Poly n)
      → (Ρ : Vec Carrier n)
      → ⟦ ⊟ xs ⟧ Ρ ≈ - ⟦ xs ⟧ Ρ
⊟-hom = ⊟-step-hom (<′-wellFounded _)
