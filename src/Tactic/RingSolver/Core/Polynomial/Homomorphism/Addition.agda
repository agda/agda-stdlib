------------------------------------------------------------------------
-- The Agda standard library
--
-- Homomorphism proofs for addition over polynomials
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Tactic.RingSolver.Core.Polynomial.Parameters

module Tactic.RingSolver.Core.Polynomial.Homomorphism.Addition
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Nat            as ℕ  using (ℕ; suc; zero; compare; _≤′_; ≤′-step; ≤′-refl)
open import Data.Nat.Properties as ℕₚ using (≤′-trans)
open import Data.Product              using (_,_; _×_; proj₂)
open import Data.List                 using (_∷_; [])
open import Data.List.Kleene
open import Data.Vec                  using (Vec)
open import Function
open import Relation.Unary

import Relation.Binary.PropositionalEquality as ≡

open Homomorphism homo hiding (_^_)
open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Lemmas homo
open import Tactic.RingSolver.Core.Polynomial.Base from
open import Tactic.RingSolver.Core.Polynomial.Reasoning to
open import Tactic.RingSolver.Core.Polynomial.Semantics homo
open import Algebra.Operations.Ring rawRing

mutual
  ⊞-hom : ∀ {n} (xs ys : Poly n) →
          ∀ ρ → ⟦ xs ⊞ ys ⟧ ρ ≈ ⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ
  ⊞-hom (xs ⊐ i≤n) (ys ⊐ j≤n) = ⊞-match-hom (inj-compare i≤n j≤n) xs ys

  ⊞-match-hom : ∀ {i j n} {i≤n : i ≤′ n} {j≤n : j ≤′ n}
                (i-cmp-j : InjectionOrdering i≤n j≤n)
                (xs : FlatPoly i) (ys : FlatPoly j) →
                ∀ ρ → ⟦ ⊞-match i-cmp-j xs ys ⟧ ρ ≈ ⟦ xs ⊐ i≤n ⟧ ρ + ⟦ ys ⊐ j≤n ⟧ ρ
  ⊞-match-hom (inj-eq ij≤n) (Κ x) (Κ y) Ρ = +-homo x y
  ⊞-match-hom (inj-eq ij≤n) (⅀ (x Δ i & xs)) (⅀ (y Δ j & ys)) Ρ =
    begin
      ⟦ ⊞-zip (compare i j) x xs y ys ⊐↓ ij≤n ⟧ Ρ
    ≈⟨ ⊐↓-hom (⊞-zip (compare i j) x xs y ys) ij≤n Ρ ⟩
      ⅀?⟦ ⊞-zip (compare i j) x xs y ys ⟧ (drop-1 ij≤n Ρ)
    ≈⟨ ⊞-zip-hom (compare i j) x xs y ys (drop-1 ij≤n Ρ) ⟩
      ⅀⟦ x Δ i & xs ⟧ (drop-1 ij≤n Ρ) + ⅀⟦ y Δ j & ys ⟧ (drop-1 ij≤n Ρ)
    ∎
  ⊞-match-hom (inj-gt i≤n j≤i-1) (⅀ xs) ys Ρ =
    let (ρ , Ρ′) = drop-1 i≤n Ρ
    in
    begin
      ⟦ ⊞-inj j≤i-1 ys xs ⊐↓ i≤n ⟧ Ρ
    ≈⟨ ⊐↓-hom (⊞-inj j≤i-1 ys xs) i≤n Ρ ⟩
      ⅀?⟦ ⊞-inj j≤i-1 ys xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ⊞-inj-hom j≤i-1 ys xs ρ Ρ′ ⟩
      ⟦ ys ⊐ j≤i-1 ⟧ (proj₂ (drop-1 i≤n Ρ)) + ⅀⟦ xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ≪+ trans-join-hom j≤i-1 i≤n ys Ρ ⟩
      ⟦ ys ⊐ (≤′-step j≤i-1 ⟨ ≤′-trans ⟩ i≤n) ⟧ Ρ + ⅀⟦ xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ +-comm _ _ ⟩
      ⅀⟦ xs ⟧ (drop-1 i≤n Ρ) + ⟦ ys ⊐ (≤′-step j≤i-1 ⟨ ≤′-trans ⟩ i≤n) ⟧ Ρ
    ∎
  ⊞-match-hom (inj-lt i≤j-1 j≤n) xs (⅀ ys) Ρ =
    let (ρ , Ρ′) = drop-1 j≤n Ρ
    in
    begin
      ⟦ ⊞-inj i≤j-1 xs ys ⊐↓ j≤n ⟧ Ρ
    ≈⟨ ⊐↓-hom (⊞-inj i≤j-1 xs ys) j≤n Ρ ⟩
      ⅀?⟦ ⊞-inj i≤j-1 xs ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ⊞-inj-hom i≤j-1 xs ys ρ Ρ′ ⟩
      ⟦ xs ⊐ i≤j-1 ⟧ (proj₂ (drop-1 j≤n Ρ)) + ⅀⟦ ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ≪+ trans-join-hom i≤j-1 j≤n xs Ρ ⟩
      ⟦ xs ⊐ (≤′-step i≤j-1 ⟨ ≤′-trans ⟩ j≤n) ⟧ Ρ + ⅀⟦ ys ⟧ (drop-1 j≤n Ρ)
    ∎

  ⊞-inj-hom : ∀ {i k}
            → (i≤k : i ≤′ k)
            → (x : FlatPoly i)
            → (ys : Coeff k +)
            → (ρ : Carrier)
            → (Ρ : Vec Carrier k)
            → ⅀?⟦ ⊞-inj i≤k x ys ⟧ (ρ , Ρ) ≈ ⟦ x ⊐ i≤k ⟧ Ρ + ⅀⟦ ys ⟧ (ρ , Ρ)
  ⊞-inj-hom i≤k xs (y ⊐ j≤k ≠0 Δ 0 & []) ρ Ρ =
    begin
      ⅀?⟦ ⊞-match (inj-compare j≤k i≤k) y xs Δ 0 ∷↓ [] ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom-0 ((⊞-match (inj-compare j≤k i≤k) y xs)) [] ρ Ρ ⟩
      ⟦ ⊞-match (inj-compare j≤k i≤k) y xs ⟧ Ρ
    ≈⟨ ⊞-match-hom (inj-compare j≤k i≤k) y xs Ρ ⟩
      (⟦ y ⊐ j≤k ⟧ Ρ + ⟦ xs ⊐ i≤k ⟧ Ρ)
    ≈⟨ +-comm _ _ ⟩
      ⟦ xs ⊐ i≤k ⟧ Ρ + ( ⟦ y ⊐ j≤k ⟧ Ρ)
    ∎
  ⊞-inj-hom i≤k xs (y ⊐ j≤k ≠0 Δ 0 & (∹ ys )) ρ Ρ =
    begin
      ⅀?⟦ ⊞-match (inj-compare j≤k i≤k) y xs Δ 0 ∷↓ (∹ ys ) ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom-0 ((⊞-match (inj-compare j≤k i≤k) y xs)) (∹ ys ) ρ Ρ ⟩
      ρ * ⅀⟦ ys ⟧ (ρ , Ρ) + ⟦ ⊞-match (inj-compare j≤k i≤k) y xs ⟧ Ρ
    ≈⟨ +≫ ⊞-match-hom (inj-compare j≤k i≤k) y xs Ρ ⟩
      ρ * ⅀⟦ ys ⟧ (ρ , Ρ) + (⟦ y ⊐ j≤k ⟧ Ρ + ⟦ xs ⊐ i≤k ⟧ Ρ)
    ≈⟨ sym (+-assoc _ _ _) ⟨ trans ⟩ +-comm _ _ ⟩
      ⟦ xs ⊐ i≤k ⟧ Ρ + (ρ * ⅀⟦ ys ⟧ (ρ , Ρ) + ⟦ y ⊐ j≤k ⟧ Ρ)
    ∎
  ⊞-inj-hom i≤k xs (y Δ suc j & ys) ρ Ρ =
    begin
      ⅀?⟦ ⊞-inj i≤k xs (y Δ suc j & ys) ⟧ (ρ , Ρ)
    ≡⟨⟩
      ⅀?⟦ xs ⊐ i≤k Δ 0 ∷↓ (∹ y Δ j & ys ) ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom-0 (xs ⊐ i≤k) (∹ y Δ j & ys ) ρ Ρ ⟩
      ρ * ⅀⟦ y Δ j & ys ⟧ (ρ , Ρ) + ⟦ xs ⊐ i≤k ⟧ Ρ
    ≈⟨ +-comm _ _ ⟩
      ⟦ xs ⊐ i≤k ⟧ Ρ + ρ * ⅀⟦ y Δ j & ys ⟧ (ρ , Ρ)
    ≈⟨ +≫ (
        begin
          ρ * ⅀⟦ y Δ j & ys ⟧ (ρ , Ρ)
        ≡⟨⟩
          ρ * (((poly y , ys) ⟦∷⟧ (ρ , Ρ)) *⟨ ρ ⟩^ j)
        ≈⟨ *≫ pow-opt _ ρ j ⟩
          ρ * (ρ ^ j * ((poly y , ys) ⟦∷⟧ (ρ , Ρ)))
        ≈⟨ sym (*-assoc ρ _ _) ⟩
          ρ * ρ ^ j * ((poly y , ys) ⟦∷⟧ (ρ , Ρ))
        ≈⟨ ≪* sym (pow-suc ρ j) ⟩
          ⅀⟦ y Δ suc j & ys ⟧ (ρ , Ρ)
        ∎) ⟩
      ⟦ xs ⊐ i≤k ⟧ Ρ + ⅀⟦ y Δ suc j & ys ⟧ (ρ , Ρ)
    ∎

  ⊞-coeffs-hom : ∀ {n} (xs : Coeff n *) (ys : Coeff n *) →
                 ∀ ρ → ⅀?⟦ ⊞-coeffs xs ys ⟧ ρ ≈ ⅀?⟦ xs ⟧ ρ + ⅀?⟦ ys ⟧ ρ
  ⊞-coeffs-hom [] ys Ρ         = sym (+-identityˡ (⅀?⟦ ys ⟧ Ρ))
  ⊞-coeffs-hom (∹ x Δ i & xs ) = ⊞-zip-r-hom i x xs

  ⊞-zip-hom : ∀ {n i j}
           → (c : ℕ.Ordering i j)
           → (x : NonZero n)
           → (xs : Coeff n *)
           → (y : NonZero n)
           → (ys : Coeff n *)
           → ∀ ρ → ⅀?⟦ ⊞-zip c x xs y ys ⟧ ρ ≈ ⅀⟦ x Δ i & xs ⟧ ρ + ⅀⟦ y Δ j & ys ⟧ ρ
  ⊞-zip-hom (ℕ.equal i) (x ≠0) xs (y ≠0) ys (ρ , Ρ) =
    let x′  = ⟦ x ⟧ Ρ
        y′  = ⟦ y ⟧ Ρ
        xs′ = ⅀?⟦ xs ⟧ (ρ , Ρ)
        ys′ = ⅀?⟦ ys ⟧ (ρ , Ρ)
    in
    begin
      ⅀?⟦ x ⊞ y Δ i ∷↓ ⊞-coeffs xs ys ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom (x ⊞ y) i (⊞-coeffs xs ys) ρ Ρ ⟩
      ρ ^ i * (((x ⊞ y) , (⊞-coeffs xs ys)) ⟦∷⟧ (ρ , Ρ))
    ≈⟨ *≫ ⟦∷⟧-hom (x ⊞ y) (⊞-coeffs xs ys) ρ Ρ ⟩
      ρ ^ i * (ρ * ⅀?⟦ ⊞-coeffs xs ys ⟧ (ρ , Ρ) + ⟦ x ⊞ y ⟧ Ρ)
    ≈⟨ *≫ begin
           ρ * ⅀?⟦ ⊞-coeffs xs ys ⟧ (ρ , Ρ) + ⟦ x ⊞ y ⟧ Ρ
          ≈⟨ (*≫ ⊞-coeffs-hom xs ys (ρ , Ρ)) ⟨ +-cong ⟩ ⊞-hom x y Ρ  ⟩
            ρ * (xs′ + ys′) + (x′ + y′)
          ≈⟨ ≪+ distribˡ ρ xs′ ys′ ⟩
            ρ * xs′ + ρ * ys′ + (x′ + y′)
          ≈⟨ +-assoc _ _ _ ⟨ trans ⟩ (+≫ (sym (+-assoc _ _ _) ⟨ trans ⟩ (≪+ +-comm _ _))) ⟩
            ρ * xs′ + (x′ + ρ * ys′ + y′)
          ≈⟨ (+≫ +-assoc _ _ _) ⟨ trans ⟩ sym (+-assoc _ _ _) ⟩
            (ρ * xs′ + x′) + (ρ * ys′ + y′)
          ∎ ⟩
     ρ ^ i * ((ρ * xs′ + x′) + (ρ * ys′ + y′))
    ≈⟨ distribˡ (ρ ^ i) _ _ ⟩
      ρ ^ i * (ρ * xs′ + x′) + ρ ^ i * (ρ * ys′ + y′)
    ≈⟨ sym (pow-opt _ ρ i ⟨ +-cong ⟩ pow-opt _ ρ i) ⟩
      (ρ * xs′ + x′) *⟨ ρ ⟩^ i + (ρ * ys′ + y′) *⟨ ρ ⟩^ i
    ≈⟨ pow-mul-cong (sym (⟦∷⟧-hom x xs ρ Ρ)) ρ i ⟨ +-cong ⟩ pow-mul-cong (sym (⟦∷⟧-hom y ys ρ Ρ)) ρ i ⟩
      ((x , xs) ⟦∷⟧ (ρ , Ρ)) *⟨ ρ ⟩^ i + ((y , ys) ⟦∷⟧ (ρ , Ρ)) *⟨ ρ ⟩^ i
    ∎
  ⊞-zip-hom (ℕ.less i k) x xs y ys (ρ , Ρ) = ⊞-zip-r-step-hom i k y ys x xs (ρ , Ρ) ⊙ +-comm _ _
  ⊞-zip-hom (ℕ.greater j k) = ⊞-zip-r-step-hom j k

  ⊞-zip-r-step-hom : ∀ {n} j k
                  → (x : NonZero n)
                  → (xs : Coeff n *)
                  → (y : NonZero n)
                  → (ys : Coeff n *)
                  → ∀ ρ → ⅀⟦ y Δ j & ⊞-zip-r x k xs ys ⟧ ρ ≈ ⅀⟦ x Δ suc (j ℕ.+ k) & xs ⟧ ρ + ⅀⟦ y Δ j & ys ⟧ ρ
  ⊞-zip-r-step-hom j k x xs y ys (ρ , Ρ) =
    let x′  = ⟦ NonZero.poly x ⟧ Ρ
        y′  = ⟦ NonZero.poly y ⟧ Ρ
        xs′ = ⅀?⟦ xs ⟧ (ρ , Ρ)
        ys′ = ⅀?⟦ ys ⟧ (ρ , Ρ)
    in
    begin
      ((poly y , ⊞-zip-r x k xs ys) ⟦∷⟧ (ρ , Ρ)) *⟨ ρ ⟩^ j
    ≈⟨ pow-mul-cong (⟦∷⟧-hom (poly y) (⊞-zip-r x k xs ys) ρ Ρ) ρ j ⟩
      (ρ * ⅀?⟦ ⊞-zip-r x k xs ys ⟧ (ρ , Ρ) + y′) *⟨ ρ ⟩^ j
    ≈⟨ pow-opt _ ρ j ⟩
      ρ ^ j * (ρ * ⅀?⟦ ⊞-zip-r x k xs ys ⟧ (ρ , Ρ) + y′)
    ≈⟨ *≫ ≪+ *≫ (⊞-zip-r-hom k x xs ys (ρ , Ρ) ⟨ trans ⟩ (≪+ pow-mul-cong (⟦∷⟧-hom (poly x) xs ρ Ρ) ρ k)) ⟩
      ρ ^ j * (ρ * ((ρ * xs′ + x′) *⟨ ρ ⟩^ k + ys′) + y′)
    ≈⟨ *≫ ≪+ distribˡ ρ _ _ ⟩
      ρ ^ j * ((ρ * (ρ * xs′ + x′) *⟨ ρ ⟩^ k + ρ * ys′) + y′)
    ≈⟨ *≫ +-assoc _ _ _ ⟩
      ρ ^ j * (ρ * (ρ * xs′ + x′) *⟨ ρ ⟩^ k + (ρ * ys′ + y′))
    ≈⟨ distribˡ _ _ _ ⟩
      ρ ^ j * (ρ * (ρ * xs′ + x′) *⟨ ρ ⟩^ k) + ρ ^ j * (ρ * ys′ + y′)
    ≈⟨ sym (pow-opt _ ρ j) ⟨ flip +-cong ⟩
         (begin
            ρ ^ j * (ρ * ((ρ * ⅀?⟦ xs ⟧ (ρ , Ρ) + ⟦ poly x ⟧ Ρ) *⟨ ρ ⟩^ k))
          ≈⟨ (sym (*-assoc _ _ _) ⟨ trans ⟩ (≪* sym (pow-sucʳ ρ j))) ⟩
            ρ ^ suc j * ((ρ * ⅀?⟦ xs ⟧ (ρ , Ρ) + ⟦ poly x ⟧ Ρ) *⟨ ρ ⟩^ k)
          ≈⟨ pow-add _ _ k j ⟩
            (ρ * ⅀?⟦ xs ⟧ (ρ , Ρ) + ⟦ poly x ⟧ Ρ) *⟨ ρ ⟩^ (k ℕ.+ suc j)
            ≡⟨ ≡.cong (λ i → (ρ * ⅀?⟦ xs ⟧ (ρ , Ρ) + ⟦ poly x ⟧ Ρ) *⟨ ρ ⟩^ i) (ℕₚ.+-comm k (suc j)) ⟩
            (ρ * ⅀?⟦ xs ⟧ (ρ , Ρ) + ⟦ poly x ⟧ Ρ) *⟨ ρ ⟩^ (suc j ℕ.+ k)
          ∎)
    ⟩
      (ρ * xs′ + x′) *⟨ ρ ⟩^ suc (j ℕ.+ k) + (ρ * ys′ + y′) *⟨ ρ ⟩^ j
    ≈⟨ pow-mul-cong (sym (⟦∷⟧-hom (poly x) xs ρ Ρ)) ρ (suc (j ℕ.+ k)) ⟨ +-cong ⟩ pow-mul-cong (sym (⟦∷⟧-hom (poly y) ys ρ Ρ)) ρ j ⟩
      ((poly x , xs) ⟦∷⟧ (ρ , Ρ)) *⟨ ρ ⟩^ suc (j ℕ.+ k) + ((poly y , ys) ⟦∷⟧ (ρ , Ρ)) *⟨ ρ ⟩^ j
    ∎

  ⊞-zip-r-hom : ∀ {n} i
             → (x : NonZero n)
             → (xs ys : Coeff n *)
             → (Ρ : Carrier × Vec Carrier n)
             → ⅀?⟦ ⊞-zip-r x i xs ys ⟧ (Ρ) ≈ ⅀⟦ x Δ i & xs ⟧ ( Ρ) + ⅀?⟦ ys ⟧ ( Ρ)
  ⊞-zip-r-hom i x xs []                (ρ , Ρ) = sym (+-identityʳ _)
  ⊞-zip-r-hom i x xs (∹ (y Δ j) & ys )         = ⊞-zip-hom (compare i j) x xs y ys
