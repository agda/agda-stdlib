------------------------------------------------------------------------
-- The Agda standard library
--
-- Homomorphism proofs for multiplication over polynomials
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Tactic.RingSolver.Core.Polynomial.Parameters

module Tactic.RingSolver.Core.Polynomial.Homomorphism.Multiplication
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Nat.Base as ℕ          using (ℕ; suc; zero; _<′_; _≤′_; ≤′-step; ≤′-refl)
open import Data.Nat.Properties    using (≤′-trans)
open import Data.Nat.Induction
open import Data.Product           using (_×_; _,_; proj₁; proj₂; map₁)
open import Data.List.Kleene
open import Data.Vec               using (Vec)
open import Function
open import Induction.WellFounded
open import Relation.Unary

open Homomorphism homo hiding (_^_)

open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Lemmas homo
open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Addition homo
open import Tactic.RingSolver.Core.Polynomial.Base from
open import Tactic.RingSolver.Core.Polynomial.Reasoning to
open import Tactic.RingSolver.Core.Polynomial.Semantics homo
open import Algebra.Operations.Ring rawRing

reassoc : ∀ {y} x z → x * (y * z) ≈ y * (x * z)
reassoc {y} x z = sym (*-assoc x y z) ⟨ trans ⟩ ((≪* *-comm x y) ⟨ trans ⟩ *-assoc y x z)

mutual
  ⊠-step′-hom : ∀ {n} → (a : Acc _<′_ n) → (xs ys : Poly n) → ∀ ρ → ⟦ ⊠-step′ a xs ys ⟧ ρ ≈ ⟦ xs ⟧ ρ * ⟦ ys ⟧ ρ
  ⊠-step′-hom a (x ⊐ p) = ⊠-step-hom a x p

  ⊠-step-hom : ∀ {i n}
             → (a : Acc _<′_ n)
             → (xs : FlatPoly i)
             → (i≤n : i ≤′ n)
             → (ys : Poly n)
             → ∀ ρ → ⟦ ⊠-step a xs i≤n ys ⟧ ρ ≈ ⟦ xs ⊐ i≤n ⟧ ρ * ⟦ ys ⟧ ρ
  ⊠-step-hom a (Κ x) i≤n = ⊠-Κ-hom a x
  ⊠-step-hom a (⅀ xs) i≤n = ⊠-⅀-hom a xs i≤n

  ⊠-Κ-hom : ∀ {n}
          → (a : Acc _<′_ n)
          → ∀ x
          → (ys : Poly n)
          → ∀ ρ
          → ⟦ ⊠-Κ a x ys ⟧ ρ ≈ ⟦ x ⟧ᵣ * ⟦ ys ⟧ ρ
  ⊠-Κ-hom (acc _)  x (Κ y  ⊐ i≤n) ρ = *-homo x y
  ⊠-Κ-hom (acc wf) x (⅀ xs ⊐ i≤n) ρ =
    begin
      ⟦ ⊠-Κ-inj (wf _ i≤n) x xs ⊐↓ i≤n ⟧ ρ
    ≈⟨ ⊐↓-hom (⊠-Κ-inj (wf _ i≤n) x xs) i≤n ρ ⟩
      ⅀?⟦ ⊠-Κ-inj (wf _ i≤n) x xs ⟧ (drop-1 i≤n ρ)
    ≈⟨ ⊠-Κ-inj-hom (wf _ i≤n) x xs (drop-1 i≤n ρ) ⟩
      ⟦ x ⟧ᵣ * ⅀⟦ xs ⟧ (drop-1 i≤n ρ)
    ∎

  ⊠-Κ-inj-hom : ∀ {n}
              → (a : Acc _<′_ n)
              → (x : Raw.Carrier)
              → (xs : Coeff n +)
              → ∀ ρ
              → ⅀?⟦ ⊠-Κ-inj a x xs ⟧ ρ ≈ ⟦ x ⟧ᵣ * ⅀⟦ xs ⟧ ρ
  ⊠-Κ-inj-hom {n} a x xs (ρ , Ρ) =
    poly-mapR
      ρ
      Ρ
      (⊠-Κ a x)
      (⟦ x ⟧ᵣ *_)
      (*-cong refl)
      reassoc
      (distribˡ ⟦ x ⟧ᵣ)
      (λ ys → ⊠-Κ-hom a x ys Ρ)
      (zeroʳ _)
      xs

  ⊠-⅀-hom : ∀ {i n}
          → (a : Acc _<′_ n)
          → (xs : Coeff i +)
          → (i<n : i <′ n)
          → (ys : Poly n)
          → ∀ ρ
          → ⟦ ⊠-⅀ a xs i<n ys ⟧ ρ ≈ ⅀⟦ xs ⟧ (drop-1 i<n ρ) * ⟦ ys ⟧ ρ
  ⊠-⅀-hom (acc wf) xs i<n (⅀ ys ⊐ j≤n) = ⊠-match-hom (acc wf) (inj-compare i<n j≤n) xs ys
  ⊠-⅀-hom (acc wf) xs i<n (Κ y  ⊐ _) ρ =
    begin
      ⟦ ⊠-Κ-inj (wf _ i<n) y xs ⊐↓ i<n ⟧ ρ
    ≈⟨ ⊐↓-hom (⊠-Κ-inj (wf _ i<n) y xs) i<n ρ ⟩
      ⅀?⟦ ⊠-Κ-inj (wf _ i<n) y xs ⟧ (drop-1 i<n ρ)
    ≈⟨ ⊠-Κ-inj-hom (wf _ i<n) y xs (drop-1 i<n ρ) ⟩
      ⟦ y ⟧ᵣ * ⅀⟦ xs ⟧ (drop-1 i<n ρ)
    ≈⟨ *-comm _ _ ⟩
      ⅀⟦ xs ⟧ (drop-1 i<n ρ) * ⟦ y ⟧ᵣ
    ∎

  ⊠-⅀-inj-hom : ∀ {i k}
              → (a : Acc _<′_ k)
              → (i<k : i <′ k)
              → (xs : Coeff i +)
              → (ys : Poly k)
              → ∀ ρ
              → ⟦ ⊠-⅀-inj a i<k xs ys ⟧ ρ ≈ ⅀⟦ xs ⟧ (drop-1 i<k ρ) * ⟦ ys ⟧ ρ
  ⊠-⅀-inj-hom (acc wf) i<k x (⅀ ys ⊐ j≤k) = ⊠-match-hom (acc wf) (inj-compare i<k j≤k) x ys
  ⊠-⅀-inj-hom (acc wf) i<k x (Κ y ⊐ j≤k) ρ =
    begin
      ⟦ ⊠-Κ-inj (wf _ i<k) y x ⊐↓ i<k ⟧ ρ
    ≈⟨ ⊐↓-hom (⊠-Κ-inj (wf _ i<k) y x) i<k ρ ⟩
      ⅀?⟦ ⊠-Κ-inj (wf _ i<k) y x ⟧ (drop-1 i<k ρ)
    ≈⟨ ⊠-Κ-inj-hom (wf _ i<k) y x (drop-1 i<k ρ) ⟩
      ⟦ y ⟧ᵣ * ⅀⟦ x ⟧ (drop-1 i<k ρ)
    ≈⟨ *-comm _ _ ⟩
      ⅀⟦ x ⟧ (drop-1 i<k ρ) * ⟦ y ⟧ᵣ
    ∎

  ⊠-match-hom : ∀ {i j n}
              → (a : Acc _<′_ n)
              → {i<n : i <′ n}
              → {j<n : j <′ n}
              → (ord : InjectionOrdering i<n j<n)
              → (xs : Coeff i +)
              → (ys : Coeff j +)
              → (Ρ : Vec Carrier n)
              → ⟦ ⊠-match a ord xs ys ⟧ Ρ
              ≈ ⅀⟦ xs ⟧ (drop-1 i<n Ρ) * ⅀⟦ ys ⟧ (drop-1 j<n Ρ)
  ⊠-match-hom {j = j} (acc wf) (inj-lt i≤j-1 j≤n) xs ys Ρ′ =
    let (ρ , Ρ) = drop-1 j≤n Ρ′
        xs′ = ⅀⟦ xs ⟧ (drop-1 (≤′-trans (≤′-step i≤j-1) j≤n) Ρ′)
    in
    begin
      ⟦ poly-map ( (⊠-⅀-inj (wf _ j≤n) i≤j-1 xs)) ys ⊐↓ j≤n ⟧ Ρ′
    ≈⟨ ⊐↓-hom (poly-map ( (⊠-⅀-inj (wf _ j≤n) i≤j-1 xs)) ys) j≤n Ρ′ ⟩
      ⅀?⟦ poly-map ( (⊠-⅀-inj (wf _ j≤n) i≤j-1 xs)) ys ⟧ (ρ , Ρ)
    ≈⟨ poly-mapR ρ Ρ (⊠-⅀-inj (wf _ j≤n) i≤j-1 xs)
                     (_ *_)
                     (*-cong refl)
                     reassoc
                     (distribˡ _)
                     (λ y → ⊠-⅀-inj-hom (wf _ j≤n) i≤j-1 xs y _)
                     (zeroʳ _) ys ⟩
       ⅀⟦ xs ⟧ (drop-1 i≤j-1 Ρ) * ⅀⟦ ys ⟧ (ρ , Ρ)
    ≈⟨ ≪* trans-join-coeffs-hom i≤j-1 j≤n xs Ρ′ ⟩
      xs′ * ⅀⟦ ys ⟧ (ρ , Ρ)
    ∎
  ⊠-match-hom (acc wf) (inj-gt i≤n j≤i-1) xs ys Ρ′ =
    let (ρ , Ρ) = drop-1 i≤n Ρ′
        ys′ = ⅀⟦ ys ⟧ (drop-1 (≤′-step j≤i-1 ⟨ ≤′-trans ⟩ i≤n) Ρ′)
    in
    begin
      ⟦ poly-map ( (⊠-⅀-inj (wf _ i≤n) j≤i-1 ys)) xs ⊐↓ i≤n ⟧ Ρ′
    ≈⟨ ⊐↓-hom (poly-map ( (⊠-⅀-inj (wf _ i≤n) j≤i-1 ys)) xs) i≤n Ρ′ ⟩
      ⅀?⟦ poly-map ( (⊠-⅀-inj (wf _ i≤n) j≤i-1 ys)) xs ⟧ (ρ , Ρ)
    ≈⟨ poly-mapR ρ Ρ (⊠-⅀-inj (wf _ i≤n) j≤i-1 ys)
                     (_ *_)
                     (*-cong refl)
                     reassoc
                     (distribˡ _)
                     (λ x → ⊠-⅀-inj-hom (wf _ i≤n) j≤i-1 ys x _)
                     (zeroʳ _) xs ⟩
      ⅀⟦ ys ⟧ (drop-1 j≤i-1 Ρ) * ⅀⟦ xs ⟧ (ρ , Ρ)
    ≈⟨ ≪* trans-join-coeffs-hom j≤i-1 i≤n ys Ρ′ ⟩
      ys′ * ⅀⟦ xs ⟧ (ρ , Ρ)
    ≈⟨ *-comm ys′ _ ⟩
      ⅀⟦ xs ⟧ (ρ , Ρ) * ys′
    ∎
  ⊠-match-hom (acc wf) (inj-eq ij≤n) xs ys Ρ =
    begin
      ⟦ ⊠-coeffs (wf _ ij≤n) xs ys ⊐↓ ij≤n ⟧ Ρ
    ≈⟨ ⊐↓-hom (⊠-coeffs (wf _ ij≤n) xs ys) ij≤n Ρ ⟩
      ⅀?⟦ ⊠-coeffs (wf _ ij≤n) xs ys ⟧ (drop-1 ij≤n Ρ)
    ≈⟨ ⊠-coeffs-hom (wf _ ij≤n) xs ys (drop-1 ij≤n Ρ) ⟩
      ⅀⟦ xs ⟧ (drop-1 ij≤n Ρ) * ⅀⟦ ys ⟧ (drop-1 ij≤n Ρ)
    ∎

  ⊠-coeffs-hom : ∀ {n}
               → (a : Acc _<′_ n)
               → (xs ys : Coeff n +)
               → ∀ ρ → ⅀?⟦ ⊠-coeffs a xs ys ⟧ ρ ≈ ⅀⟦ xs ⟧ ρ * ⅀⟦ ys ⟧ ρ
  ⊠-coeffs-hom a xs (y ≠0 Δ j & []) (ρ , Ρ) =
    begin
      ⅀?⟦ poly-map (⊠-step′ a y) xs ⍓* j ⟧ (ρ , Ρ)
    ≈⟨ sym (pow′-hom j (poly-map (⊠-step′ a y) xs) ρ Ρ) ⟩
      ⅀?⟦ poly-map (⊠-step′ a y) xs ⟧ (ρ , Ρ) *⟨ ρ ⟩^ j
    ≈⟨ pow-mul-cong (poly-mapR ρ Ρ (⊠-step′ a y) (⟦ y ⟧ Ρ *_) (*-cong refl) reassoc (distribˡ _) (λ z → ⊠-step′-hom a y z Ρ) (zeroʳ _) xs) ρ j ⟩
      (⟦ y ⟧ Ρ * ⅀⟦ xs ⟧ (ρ , Ρ)) *⟨ ρ ⟩^ j
    ≈⟨ pow-opt _ ρ j ⟩
      (ρ ^ j) * (⟦ y ⟧ Ρ * ⅀⟦ xs ⟧ (ρ , Ρ))
    ≈⟨ sym (*-assoc _ _ _) ⟩
      (ρ ^ j) * ⟦ y ⟧ Ρ * ⅀⟦ xs ⟧ (ρ , Ρ)
    ≈⟨ *-comm _ _ ⟩
      ⅀⟦ xs ⟧ (ρ , Ρ) * ((ρ ^ j) * ⟦ y ⟧ Ρ)
    ≈⟨ *≫ sym (pow-opt _ ρ j) ⟩
      ⅀⟦ xs ⟧ (ρ , Ρ) * (⟦ y ⟧ Ρ *⟨ ρ ⟩^ j)
    ∎
  ⊠-coeffs-hom a xs (y ≠0 Δ j & ∹ ys) (ρ , Ρ) =
    let xs′ = ⅀⟦ xs ⟧ (ρ , Ρ)
        y′  = ⟦ y ⟧ Ρ
        ys′ = ⅀⟦ ys ⟧ (ρ , Ρ)
    in
    begin
      ⅀?⟦ para (⊠-cons a y ys) xs ⍓* j ⟧ (ρ , Ρ)
    ≈⟨ sym (pow′-hom j (para (⊠-cons a y ys) xs) ρ Ρ) ⟨ trans ⟩ pow-opt _ ρ j ⟩
      ρ ^ j * ⅀?⟦ para (⊠-cons a y ys) xs ⟧ (ρ , Ρ)
    ≈⟨ *≫ ⊠-cons-hom a y ys xs ρ Ρ ⟩
     ρ ^ j * (xs′ * (ρ * ys′ + y′))
    ≈⟨ sym (*-assoc _ _ _) ⟨ trans ⟩ (≪* *-comm _ _) ⟨ trans ⟩ *-assoc _ _ _ ⟨ trans ⟩ (*≫ sym (pow-opt _ ρ j))⟩
      xs′ * ((ρ * ys′ + y′) *⟨ ρ ⟩^ j)
    ∎

  ⊠-cons-hom : ∀ {n}
             → (a : Acc _<′_ n)
             → (y : Poly n)
             → (ys xs : Coeff n +)
             → (ρ : Carrier)
             → (Ρ : Vec Carrier n)
             → ⅀?⟦ para (⊠-cons a y ys) xs ⟧ (ρ , Ρ)
             ≈ ⅀⟦ xs ⟧ (ρ , Ρ) * (ρ * ⅀⟦ ys ⟧ (ρ , Ρ) + ⟦ y ⟧ Ρ)
  -- ⊠-cons-hom a y [] xs ρ Ρ = {!!}
  ⊠-cons-hom a y ys xs ρ Ρ = poly-foldR ρ Ρ (⊠-cons a y ys) (flip _*_ (ρ * ⅀⟦ ys ⟧ (ρ , Ρ) + ⟦ y ⟧ Ρ)) (flip *-cong refl) (λ x y → sym (*-assoc x y _)) step (zeroˡ _) xs
    where
    step = λ { (z ⊐ j≤n) {ys₁} zs ys≋zs →
      let x′  = ⟦ z ⊐ j≤n ⟧ Ρ
          xs′ = ⅀?⟦ zs ⟧ (ρ , Ρ)
          y′  = ⟦ y ⟧ Ρ
          ys′ = ⅀⟦ ys ⟧ (ρ , Ρ)
          step = λ y → ⊠-step-hom a z j≤n y Ρ
      in
      begin
        ρ * ⅀?⟦ ⊞-coeffs (poly-map ( (⊠-step a z j≤n)) ys) ys₁ ⟧ (ρ , Ρ) + ⟦ ⊠-step a z j≤n y ⟧ Ρ
      ≈⟨ (*≫ ⊞-coeffs-hom (poly-map (⊠-step a z j≤n) ys) _ (ρ , Ρ)) ⟨ +-cong ⟩ ⊠-step-hom a z j≤n y Ρ ⟩
        ρ * (⅀?⟦ poly-map (⊠-step a z j≤n) ys ⟧ (ρ , Ρ) + ⅀?⟦ ys₁ ⟧ (ρ , Ρ)) + x′ * y′
      ≈⟨ ≪+ *≫ (poly-mapR ρ Ρ (⊠-step a z j≤n) (x′ *_) (*-cong refl) reassoc (distribˡ _) step (zeroʳ _) ys ⟨ +-cong ⟩ ys≋zs) ⟩
        ρ * (x′ * ys′ + xs′ * (ρ * ys′ + y′)) + (x′ * y′)
      ≈⟨ ≪+ distribˡ _ _ _ ⟩
        ρ * (x′ * ys′) + ρ * (xs′ * (ρ * ys′ + y′)) + (x′ * y′)
      ≈⟨ (≪+ +-comm _ _) ⟨ trans ⟩ +-assoc _ _ _ ⟩
        ρ * (xs′ * (ρ * ys′ + y′)) + (ρ * (x′ * ys′) + (x′ * y′))
      ≈⟨ sym (*-assoc _ _ _) ⟨ +-cong ⟩ ((≪+ (sym (*-assoc _ _ _) ⟨ trans ⟩ (≪* *-comm _ _) ⟨ trans ⟩ *-assoc _ _ _)) ⟨ trans ⟩ sym (distribˡ _ _ _)) ⟩
        ρ * xs′ * (ρ * ys′ + y′) + x′ * (ρ * ys′ + y′)
      ≈⟨ sym (distribʳ _ _ _) ⟩
        (ρ * xs′ + x′) * (ρ * ys′ + y′)
      ∎ }

⊠-hom : ∀ {n} (xs ys : Poly n) →
        ∀ ρ → ⟦ xs ⊠ ys ⟧ ρ ≈ ⟦ xs ⟧ ρ * ⟦ ys ⟧ ρ
⊠-hom (xs ⊐ i≤n) = ⊠-step-hom (<′-wellFounded _) xs i≤n
