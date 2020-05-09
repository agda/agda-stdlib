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

import Algebra.Operations.Ring rawRing as RawPow
import Algebra.Operations.Ring (RawCoeff.rawRing from) as CoPow

pow-eval-hom : ∀ x i → ⟦ x CoPow.^ i +1 ⟧ᵣ ≈ ⟦ x ⟧ᵣ RawPow.^ i +1
pow-eval-hom x ℕ.zero = refl
pow-eval-hom x (suc i) = (*-homo _ x) ⟨ trans ⟩ (≪* pow-eval-hom x i)

⊡-mult-hom : ∀ {n} i (xs : Poly n) ρ → ⟦ ⊡-mult i xs ⟧ ρ ≈ ⟦ xs ⟧ ρ RawPow.^ i +1
⊡-mult-hom ℕ.zero xs ρ = refl
⊡-mult-hom (suc i) xs ρ =  ⊠-hom (⊡-mult i xs) xs ρ ⟨ trans ⟩ (≪* ⊡-mult-hom i xs ρ)

⊡-+1-hom : ∀ {n} → (xs : Poly n) → (i : ℕ) → ∀ ρ → ⟦ xs ⊡ i +1 ⟧ ρ ≈ ⟦ xs ⟧ ρ RawPow.^ i +1
⊡-+1-hom (Κ x  ⊐ i≤n) i ρ = pow-eval-hom x i
⊡-+1-hom xs@(⅀ (_ & ∹ _) ⊐ i≤n) i ρ = ⊡-mult-hom i xs ρ
⊡-+1-hom (⅀ (x ≠0 Δ j & []) ⊐ i≤n) i ρ =
  begin
    ⟦ x ⊡ i +1 Δ (j ℕ.+ i ℕ.* j) ∷↓ [] ⊐↓ i≤n ⟧ ρ
  ≈⟨ ⊐↓-hom (x ⊡ i +1 Δ (j ℕ.+ i ℕ.* j) ∷↓ []) i≤n ρ ⟩
    ⅀?⟦ x ⊡ i +1 Δ (j ℕ.+ i ℕ.* j) ∷↓ [] ⟧ (drop-1 i≤n ρ)
  ≈⟨ ∷↓-hom (x ⊡ i +1) (j ℕ.+ i ℕ.* j) [] ρ′ Ρ ⟩
    (ρ′ RawPow.^ (j ℕ.+ i ℕ.* j)) * (⟦ x ⊡ i +1 ⟧ Ρ)
  ≈⟨ *≫ (( ⊡-+1-hom x i Ρ) ) ⟩
    (ρ′ RawPow.^ (j ℕ.+ i ℕ.* j)) * (⟦ x ⟧ Ρ RawPow.^ i +1)
  ≈⟨ rearrange j ⟩
    (( ⟦ x ⟧ Ρ) *⟨ ρ′ ⟩^ j) RawPow.^ i +1
  ∎
  where
  ρ′,Ρ = drop-1 i≤n ρ
  ρ′ = proj₁ ρ′,Ρ
  Ρ = proj₂ ρ′,Ρ
  rearrange : ∀ j → (ρ′ RawPow.^ (j ℕ.+ i ℕ.* j)) * (⟦ x ⟧ Ρ RawPow.^ i +1)≈ (( ⟦ x ⟧ Ρ) *⟨ ρ′ ⟩^ j) RawPow.^ i +1
  rearrange zero =
    begin
      (ρ′ RawPow.^ (i ℕ.* 0)) * (⟦ x ⟧ Ρ RawPow.^ i +1)
    ≡⟨ ≡.cong (λ k →  (ρ′ RawPow.^ k) * (⟦ x ⟧ Ρ RawPow.^ i +1)) (ℕ-Prop.*-zeroʳ i) ⟩
      1# * (⟦ x ⟧ Ρ RawPow.^ i +1)
    ≈⟨ *-identityˡ _ ⟩
      ⟦ x ⟧ Ρ RawPow.^ i +1
    ∎
  rearrange j@(suc j′) =
    begin
      (ρ′ RawPow.^ (j ℕ.+ i ℕ.* j)) * (⟦ x ⟧ Ρ RawPow.^ i +1)
    ≈⟨ ≪* sym ( pow-mult-+1 ρ′ j′ i) ⟩
      ((ρ′ RawPow.^ j′ +1) RawPow.^ i +1) * (⟦ x ⟧ Ρ RawPow.^ i +1)
    ≈⟨ sym (pow-distrib-+1 _ (⟦ x ⟧ Ρ) i) ⟩
      ((ρ′ RawPow.^ j′ +1) * ⟦ x ⟧ Ρ) RawPow.^ i +1
    ∎

⊡-hom : ∀ {n} → (xs : Poly n) → (i : ℕ) → ∀ ρ → ⟦ xs ⊡ i ⟧ ρ ≈ ⟦ xs ⟧ ρ RawPow.^ i
⊡-hom xs ℕ.zero ρ = 1-homo
⊡-hom xs (suc i) ρ = ⊡-+1-hom xs i ρ
