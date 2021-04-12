------------------------------------------------------------------------
-- The Agda standard library
--
-- Homomorphism proofs for exponentiation over polynomials
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Tactic.RingSolver.Core.Polynomial.Parameters

module Tactic.RingSolver.Core.Polynomial.Homomorphism.Exponentiation
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Function

open import Data.Nat.Base as ℕ using (ℕ; suc; zero; compare)
open import Data.Product  using (_,_; _×_; proj₁; proj₂)
open import Data.List.Kleene
open import Data.Vec      using (Vec)

import Data.Nat.Properties as ℕ-Prop
import Relation.Binary.PropositionalEquality as ≡

open Homomorphism homo
open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Lemmas homo
open import Tactic.RingSolver.Core.Polynomial.Base from
open import Tactic.RingSolver.Core.Polynomial.Reasoning to
open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Multiplication homo
open import Tactic.RingSolver.Core.Polynomial.Semantics homo

import Algebra.Properties.CommutativeSemiring.Exp.TCOptimised commutativeSemiring as RawPow
import Algebra.Definitions.RawSemiring (RawCoeff.rawSemiring from) as CoPow

pow-eval-hom : ∀ x i → ⟦ x CoPow.^′ suc i ⟧ᵣ ≈ ⟦ x ⟧ᵣ RawPow.^ suc i
pow-eval-hom x zero    = refl
pow-eval-hom x (suc i) = (*-homo _ x) ⟨ trans ⟩ (≪* pow-eval-hom x i)

⊡-mult-hom : ∀ {n} i (xs : Poly n) ρ → ⟦ ⊡-mult i xs ⟧ ρ ≈ ⟦ xs ⟧ ρ RawPow.^ suc i
⊡-mult-hom zero    xs ρ = refl
⊡-mult-hom (suc i) xs ρ =  ⊠-hom (⊡-mult i xs) xs ρ ⟨ trans ⟩ (≪* ⊡-mult-hom i xs ρ)

⊡-+1-hom : ∀ {n} → (xs : Poly n) → (i : ℕ) → ∀ ρ → ⟦ xs ⊡ i +1 ⟧ ρ ≈ ⟦ xs ⟧ ρ RawPow.^ suc i
⊡-+1-hom (Κ x  ⊐ i≤n)           i ρ = pow-eval-hom x i
⊡-+1-hom xs@(⅀ (_ & ∹ _) ⊐ i≤n) i ρ = ⊡-mult-hom i xs ρ
⊡-+1-hom (⅀ (x ≠0 Δ j & []) ⊐ i≤n) i ρ =
  begin
    ⟦ x ⊡ i +1 Δ (j ℕ.+ i ℕ.* j) ∷↓ [] ⊐↓ i≤n ⟧ ρ
  ≈⟨ ⊐↓-hom (x ⊡ i +1 Δ (j ℕ.+ i ℕ.* j) ∷↓ []) i≤n ρ ⟩
    ⅀?⟦ x ⊡ i +1 Δ (j ℕ.+ i ℕ.* j) ∷↓ [] ⟧ (drop-1 i≤n ρ)
  ≈⟨ ∷↓-hom (x ⊡ i +1) (j ℕ.+ i ℕ.* j) [] ρ′ Ρ ⟩
    (ρ′ RawPow.^ (j ℕ.+ i ℕ.* j)) * (⟦ x ⊡ i +1 ⟧ Ρ)
  ≈⟨ *≫ (( ⊡-+1-hom x i Ρ) ) ⟩
    (ρ′ RawPow.^ (j ℕ.+ i ℕ.* j)) * (⟦ x ⟧ Ρ RawPow.^ suc i)
  ≈⟨ rearrange j ⟩
    (( ⟦ x ⟧ Ρ) *⟨ ρ′ ⟩^ j) RawPow.^ suc i
  ∎
  where
  ρ′,Ρ = drop-1 i≤n ρ
  ρ′ = proj₁ ρ′,Ρ
  Ρ = proj₂ ρ′,Ρ
  rearrange : ∀ j → (ρ′ RawPow.^ (j ℕ.+ i ℕ.* j)) * (⟦ x ⟧ Ρ RawPow.^ suc i)≈ (( ⟦ x ⟧ Ρ) *⟨ ρ′ ⟩^ j) RawPow.^ suc i
  rearrange zero =
    begin
      (ρ′ RawPow.^ (i ℕ.* 0)) * (⟦ x ⟧ Ρ RawPow.^ suc i)
    ≡⟨ ≡.cong (λ k →  (ρ′ RawPow.^ k) * (⟦ x ⟧ Ρ RawPow.^ suc i)) (ℕ-Prop.*-zeroʳ i) ⟩
      1# * (⟦ x ⟧ Ρ RawPow.^ suc i)
    ≈⟨ *-identityˡ _ ⟩
      ⟦ x ⟧ Ρ RawPow.^ suc i
    ∎
  rearrange j@(suc j′) =
    begin
      (ρ′ RawPow.^ (suc i ℕ.* j))           * (⟦ x ⟧ Ρ RawPow.^ suc i)
    ≡⟨ ≡.cong (λ v → (ρ′ RawPow.^ v) * (⟦ x ⟧ Ρ RawPow.^ suc i)) (ℕ-Prop.*-comm (suc i) j) ⟩
      (ρ′ RawPow.^ (j ℕ.* suc i))           * (⟦ x ⟧ Ρ RawPow.^ suc i)
    ≈⟨ ≪* sym (RawPow.^-assocʳ ρ′ j (suc i)) ⟩
      ((ρ′ RawPow.^ suc j′) RawPow.^ suc i) * (⟦ x ⟧ Ρ RawPow.^ suc i)
    ≈⟨ sym (RawPow.^-distrib-* _ (⟦ x ⟧ Ρ) (suc i)) ⟩
      ((ρ′ RawPow.^ suc j′) * ⟦ x ⟧ Ρ) RawPow.^ suc i
    ∎

⊡-hom : ∀ {n} → (xs : Poly n) → (i : ℕ) → ∀ ρ → ⟦ xs ⊡ i ⟧ ρ ≈ ⟦ xs ⟧ ρ RawPow.^ i
⊡-hom xs 0       ρ = 1-homo
⊡-hom xs (suc i) ρ = ⊡-+1-hom xs i ρ
