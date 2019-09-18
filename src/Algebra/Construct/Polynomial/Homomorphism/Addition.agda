{-# OPTIONS --without-K --safe #-}

open import Algebra.Construct.Polynomial.Parameters

module Algebra.Construct.Polynomial.Homomorphism.Addition
  {r₁ r₂ r₃}
  (homo : Homomorphism r₁ r₂ r₃)
  where

open import Function

open import Data.Nat as ℕ using (ℕ; suc; zero; compare; _≤′_; ≤′-step; ≤′-refl)
open import Data.Nat.Properties using (≤′-trans)
open import Data.Product  using (_,_; _×_; proj₂)
open import Data.List     using (_∷_; [])
open import Data.Vec      using (Vec)

import Data.Nat.Properties as ℕ-Prop
import Relation.Binary.PropositionalEquality as ≡

open Homomorphism homo
open import Algebra.Construct.Polynomial.Homomorphism.Lemmas homo
open import Algebra.Construct.Polynomial.Base from
open import Algebra.Construct.Polynomial.Reasoning to
open import Algebra.Construct.Polynomial.Semantics homo
open import Algebra.Operations.Ring.Compact rawRing
open import Data.List.Kleene
open import Relation.Unary

mutual
  ⊞-hom : ∀ {n}
        → (xs : Poly n)
        → (ys : Poly n)
        → ∀ ρ → ⟦ xs ⊞ ys ⟧ ρ ≈ ⟦ xs ⟧ ρ + ⟦ ys ⟧ ρ
  ⊞-hom (xs Π i≤n) (ys Π j≤n) = ⊞-match-hom (inj-compare i≤n j≤n) xs ys

  ⊞-match-hom : ∀ {i j n}
              → {i≤n : i ≤′ n}
              → {j≤n : j ≤′ n}
              → (i-cmp-j : InjectionOrdering i≤n j≤n)
              → (xs : FlatPoly i)
              → (ys : FlatPoly j)
              → ∀ ρ → ⟦ ⊞-match i-cmp-j xs ys ⟧ ρ ≈ ⟦ xs Π i≤n ⟧ ρ + ⟦ ys Π j≤n ⟧ ρ
  ⊞-match-hom (inj-eq ij≤n) (Κ x) (Κ y) Ρ = +-homo x y
  ⊞-match-hom (inj-eq ij≤n) (Σ (x Δ i & xs)) (Σ (y Δ j & ys)) Ρ =
    begin
      ⟦ ⊞-zip (compare i j) x xs y ys Π↓ ij≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊞-zip (compare i j) x xs y ys) ij≤n Ρ ⟩
      Σ?⟦ ⊞-zip (compare i j) x xs y ys ⟧ (drop-1 ij≤n Ρ)
    ≈⟨ ⊞-zip-hom (compare i j) x xs y ys (drop-1 ij≤n Ρ) ⟩
      Σ⟦ x Δ i & xs ⟧ (drop-1 ij≤n Ρ) + Σ⟦ y Δ j & ys ⟧ (drop-1 ij≤n Ρ)
    ∎
  ⊞-match-hom (inj-gt i≤n j≤i-1) (Σ xs) ys Ρ =
    let (ρ , Ρ′) = drop-1 i≤n Ρ
    in
    begin
      ⟦ ⊞-inj j≤i-1 ys xs Π↓ i≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊞-inj j≤i-1 ys xs) i≤n Ρ ⟩
      Σ?⟦ ⊞-inj j≤i-1 ys xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ⊞-inj-hom j≤i-1 ys xs ρ Ρ′ ⟩
      ⟦ ys Π j≤i-1 ⟧ (proj₂ (drop-1 i≤n Ρ)) + Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ≪+ trans-join-hom j≤i-1 i≤n ys Ρ ⟩
      ⟦ ys Π (≤′-step j≤i-1 ⟨ ≤′-trans ⟩ i≤n) ⟧ Ρ + Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ +-comm _ _ ⟩
      Σ⟦ xs ⟧ (drop-1 i≤n Ρ) + ⟦ ys Π (≤′-step j≤i-1 ⟨ ≤′-trans ⟩ i≤n) ⟧ Ρ
    ∎
  ⊞-match-hom (inj-lt i≤j-1 j≤n) xs (Σ ys) Ρ =
    let (ρ , Ρ′) = drop-1 j≤n Ρ
    in
    begin
      ⟦ ⊞-inj i≤j-1 xs ys Π↓ j≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊞-inj i≤j-1 xs ys) j≤n Ρ ⟩
      Σ?⟦ ⊞-inj i≤j-1 xs ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ⊞-inj-hom i≤j-1 xs ys ρ Ρ′ ⟩
      ⟦ xs Π i≤j-1 ⟧ (proj₂ (drop-1 j≤n Ρ)) + Σ⟦ ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ≪+ trans-join-hom i≤j-1 j≤n xs Ρ ⟩
      ⟦ xs Π (≤′-step i≤j-1 ⟨ ≤′-trans ⟩ j≤n) ⟧ Ρ + Σ⟦ ys ⟧ (drop-1 j≤n Ρ)
    ∎

  ⊞-inj-hom : ∀ {i k}
            → (i≤k : i ≤′ k)
            → (x : FlatPoly i)
            → (ys : Coeff k +)
            → (ρ : Carrier)
            → (Ρ : Vec Carrier k)
            → Σ?⟦ ⊞-inj i≤k x ys ⟧ (ρ , Ρ) ≈ ⟦ x Π i≤k ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ)
  ⊞-inj-hom i≤k xs (y Π j≤k ≠0 Δ 0 & []) ρ Ρ =
    begin
      Σ?⟦ ⊞-match (inj-compare j≤k i≤k) y xs Δ 0 ∷↓ [] ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom-0 ((⊞-match (inj-compare j≤k i≤k) y xs)) [] ρ Ρ ⟩
      ⟦ ⊞-match (inj-compare j≤k i≤k) y xs ⟧ Ρ
    ≈⟨ ⊞-match-hom (inj-compare j≤k i≤k) y xs Ρ ⟩
      (⟦ y Π j≤k ⟧ Ρ + ⟦ xs Π i≤k ⟧ Ρ)
    ≈⟨ +-comm _ _ ⟩
      ⟦ xs Π i≤k ⟧ Ρ + ( ⟦ y Π j≤k ⟧ Ρ)
    ∎
  ⊞-inj-hom i≤k xs (y Π j≤k ≠0 Δ 0 & (∹ ys )) ρ Ρ =
    begin
      Σ?⟦ ⊞-match (inj-compare j≤k i≤k) y xs Δ 0 ∷↓ (∹ ys ) ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom-0 ((⊞-match (inj-compare j≤k i≤k) y xs)) (∹ ys ) ρ Ρ ⟩
      ρ * Σ⟦ ys ⟧ (ρ , Ρ) + ⟦ ⊞-match (inj-compare j≤k i≤k) y xs ⟧ Ρ
    ≈⟨ +≫ ⊞-match-hom (inj-compare j≤k i≤k) y xs Ρ ⟩
      ρ * Σ⟦ ys ⟧ (ρ , Ρ) + (⟦ y Π j≤k ⟧ Ρ + ⟦ xs Π i≤k ⟧ Ρ)
    ≈⟨ sym (+-assoc _ _ _) ⟨ trans ⟩ +-comm _ _ ⟩
      ⟦ xs Π i≤k ⟧ Ρ + (ρ * Σ⟦ ys ⟧ (ρ , Ρ) + ⟦ y Π j≤k ⟧ Ρ)
    ∎
  ⊞-inj-hom i≤k xs (y Δ suc j & ys) ρ Ρ =
    let y′ = NonZero.poly y
    in
    begin
      Σ?⟦ ⊞-inj i≤k xs (y Δ suc j & ys) ⟧ (ρ , Ρ)
    ≡⟨⟩
      Σ?⟦ xs Π i≤k Δ 0 ∷↓ (∹ y Δ j & ys ) ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom-0 (xs Π i≤k) (∹ y Δ j & ys ) ρ Ρ ⟩
      ρ * Σ⟦ y Δ j & ys ⟧ (ρ , Ρ) + ⟦ xs Π i≤k ⟧ Ρ
    ≈⟨ +-comm _ _ ⟩
      ⟦ xs Π i≤k ⟧ Ρ + ρ * Σ⟦ y Δ j & ys ⟧ (ρ , Ρ)
    ≈⟨ +≫ (
        begin
          ρ * Σ⟦ y Δ j & ys ⟧ (ρ , Ρ)
        ≡⟨⟩
          ρ * (((poly y , ys) ⟦∷⟧ (ρ , Ρ)) *⟨ ρ ⟩^ j)
        ≈⟨ *≫ pow-opt _ ρ j ⟩
          ρ * (ρ ^ j * ((poly y , ys) ⟦∷⟧ (ρ , Ρ)))
        ≈⟨ sym (*-assoc ρ _ _) ⟩
          ρ * ρ ^ j * ((poly y , ys) ⟦∷⟧ (ρ , Ρ))
        ≈⟨ ≪* sym (pow-suc ρ j) ⟩
          Σ⟦ y Δ suc j & ys ⟧ (ρ , Ρ)
        ∎) ⟩
      ⟦ xs Π i≤k ⟧ Ρ + Σ⟦ y Δ suc j & ys ⟧ (ρ , Ρ)
    ∎

  ⊞-coeffs-hom : ∀ {n}
              → (xs : Coeff n *)
              → (ys : Coeff n *)
              → ∀ ρ → Σ?⟦ ⊞-coeffs xs ys ⟧ ρ ≈ Σ?⟦ xs ⟧ ρ + Σ?⟦ ys ⟧ ρ
  ⊞-coeffs-hom [] ys Ρ = sym (+-identityˡ (Σ?⟦ ys ⟧ Ρ))
  ⊞-coeffs-hom (∹ x Δ i & xs ) = ⊞-zip-r-hom i x xs

  ⊞-zip-hom : ∀ {n i j}
           → (c : ℕ.Ordering i j)
           → (x : NonZero n)
           → (xs : Coeff n *)
           → (y : NonZero n)
           → (ys : Coeff n *)
           → ∀ ρ → Σ?⟦ ⊞-zip c x xs y ys ⟧ ρ ≈ Σ⟦ x Δ i & xs ⟧ ρ + Σ⟦ y Δ j & ys ⟧ ρ
  ⊞-zip-hom (ℕ.equal i) (x ≠0) xs (y ≠0) ys (ρ , Ρ) =
    let x′  = ⟦ x ⟧ Ρ
        y′  = ⟦ y ⟧ Ρ
        xs′ = Σ?⟦ xs ⟧ (ρ , Ρ)
        ys′ = Σ?⟦ ys ⟧ (ρ , Ρ)
    in
    begin
      Σ?⟦ x ⊞ y Δ i ∷↓ ⊞-coeffs xs ys ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom (x ⊞ y) i (⊞-coeffs xs ys) ρ Ρ ⟩
      ρ ^ i * (((x ⊞ y) , (⊞-coeffs xs ys)) ⟦∷⟧ (ρ , Ρ))
    ≈⟨ *≫ ⟦∷⟧-hom (x ⊞ y) (⊞-coeffs xs ys) ρ Ρ ⟩
      ρ ^ i * (ρ * Σ?⟦ ⊞-coeffs xs ys ⟧ (ρ , Ρ) + ⟦ x ⊞ y ⟧ Ρ)
    ≈⟨ *≫ begin
           ρ * Σ?⟦ ⊞-coeffs xs ys ⟧ (ρ , Ρ) + ⟦ x ⊞ y ⟧ Ρ
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
                  → ∀ ρ → Σ⟦ y Δ j & ⊞-zip-r x k xs ys ⟧ ρ ≈ Σ⟦ x Δ suc (j ℕ.+ k) & xs ⟧ ρ + Σ⟦ y Δ j & ys ⟧ ρ
  ⊞-zip-r-step-hom j k x xs y ys (ρ , Ρ) =
    let x′  = ⟦ NonZero.poly x ⟧ Ρ
        y′  = ⟦ NonZero.poly y ⟧ Ρ
        xs′ = Σ?⟦ xs ⟧ (ρ , Ρ)
        ys′ = Σ?⟦ ys ⟧ (ρ , Ρ)
    in
    begin
      ((poly y , ⊞-zip-r x k xs ys) ⟦∷⟧ (ρ , Ρ)) *⟨ ρ ⟩^ j
    ≈⟨ pow-mul-cong (⟦∷⟧-hom (poly y) (⊞-zip-r x k xs ys) ρ Ρ) ρ j ⟩
      (ρ * Σ?⟦ ⊞-zip-r x k xs ys ⟧ (ρ , Ρ) + y′) *⟨ ρ ⟩^ j
    ≈⟨ pow-opt _ ρ j ⟩
      ρ ^ j * (ρ * Σ?⟦ ⊞-zip-r x k xs ys ⟧ (ρ , Ρ) + y′)
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
            ρ ^ j * (ρ * ((ρ * Σ?⟦ xs ⟧ (ρ , Ρ) + ⟦ poly x ⟧ Ρ) *⟨ ρ ⟩^ k))
          ≈⟨ (sym (*-assoc _ _ _) ⟨ trans ⟩ (≪* sym (pow-sucʳ ρ j))) ⟩
            ρ ^ suc j * ((ρ * Σ?⟦ xs ⟧ (ρ , Ρ) + ⟦ poly x ⟧ Ρ) *⟨ ρ ⟩^ k)
          ≈⟨ pow-add _ _ k j ⟩
            (ρ * Σ?⟦ xs ⟧ (ρ , Ρ) + ⟦ poly x ⟧ Ρ) *⟨ ρ ⟩^ (k ℕ.+ suc j)
            ≡⟨ ≡.cong (λ i → (ρ * Σ?⟦ xs ⟧ (ρ , Ρ) + ⟦ poly x ⟧ Ρ) *⟨ ρ ⟩^ i) (ℕ-Prop.+-comm k (suc j)) ⟩
            (ρ * Σ?⟦ xs ⟧ (ρ , Ρ) + ⟦ poly x ⟧ Ρ) *⟨ ρ ⟩^ (suc j ℕ.+ k)
          ∎)
    ⟩
      (ρ * xs′ + x′) *⟨ ρ ⟩^ suc (j ℕ.+ k) + (ρ * ys′ + y′) *⟨ ρ ⟩^ j
    ≈⟨ pow-mul-cong (sym (⟦∷⟧-hom (poly x) xs ρ Ρ)) ρ (suc (j ℕ.+ k)) ⟨ +-cong ⟩ pow-mul-cong (sym (⟦∷⟧-hom (poly y) ys ρ Ρ)) ρ j ⟩
      ((poly x , xs) ⟦∷⟧ (ρ , Ρ)) *⟨ ρ ⟩^ suc (j ℕ.+ k) + ((poly y , ys) ⟦∷⟧ (ρ , Ρ)) *⟨ ρ ⟩^ j
    ∎

  ⊞-zip-r-hom : ∀ {n} i
             → (x : NonZero n)
             → (xs : Coeff n *)
             → (ys : Coeff n *)
             → (Ρ : Carrier × Vec Carrier n)
             → Σ?⟦ ⊞-zip-r x i xs ys ⟧ (Ρ) ≈ Σ⟦ x Δ i & xs ⟧ ( Ρ) + Σ?⟦ ys ⟧ ( Ρ)
  ⊞-zip-r-hom i x xs [] (ρ , Ρ) = sym (+-identityʳ _)
  ⊞-zip-r-hom i x xs (∹ (y Δ j) & ys ) = ⊞-zip-hom (compare i j) x xs y ys
