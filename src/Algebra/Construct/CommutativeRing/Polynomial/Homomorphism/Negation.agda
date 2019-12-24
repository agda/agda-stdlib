{-# OPTIONS --without-K --safe #-}

open import Algebra.Construct.CommutativeRing.Polynomial.Parameters

module Algebra.Construct.CommutativeRing.Polynomial.Homomorphism.Negation
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Product          using (_,_)
open import Data.Vec              using (Vec)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat         using (<′-wellFounded)
open import Data.Nat using (_<′_)

open import Function

open Homomorphism homo
open import Algebra.Construct.CommutativeRing.Polynomial.Homomorphism.Lemmas homo
open import Algebra.Construct.CommutativeRing.Polynomial.Reasoning to
open import Algebra.Construct.CommutativeRing.Polynomial.Base from
open import Algebra.Construct.CommutativeRing.Polynomial.Semantics homo

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
    ⟦ poly-map (⊟-step (wf _ i≤n)) xs ⊐↓ i≤n ⟧ ρ′
  ≈⟨ ⊐↓-hom (poly-map (⊟-step (wf _ i≤n)) xs) i≤n ρ′ ⟩
    ⅀?⟦ poly-map (⊟-step  (wf _ i≤n)) xs ⟧ (ρ , ρs)
  ≈⟨ poly-mapR ρ ρs (⊟-step (wf _ i≤n)) -_ (-‿cong) (λ x y → *-comm x (- y) ⟨ trans ⟩ -‿*-distribˡ y x ⟨ trans ⟩ -‿cong (*-comm _ _)) (λ x y → sym (-‿+-comm x y)) (flip (⊟-step-hom (wf _ i≤n)) ρs) (sym neg-zero ) xs ⟩
    - ⅀⟦ xs ⟧ (ρ , ρs)
  ∎

⊟-hom : ∀ {n}
      → (xs : Poly n)
      → (Ρ : Vec Carrier n)
      → ⟦ ⊟ xs ⟧ Ρ ≈ - ⟦ xs ⟧ Ρ
⊟-hom = ⊟-step-hom (<′-wellFounded _)
