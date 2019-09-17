{-# OPTIONS --without-K --safe #-}

open import Algebra.Construct.Polynomial.Parameters

module Algebra.Construct.Polynomial.Homomorphism.Multiplication
  {r₁ r₂ r₃}
  (homo : Homomorphism r₁ r₂ r₃)
  where

open import Data.Nat as ℕ          using (ℕ; suc; zero; _<′_; _≤′_)
open import Data.Product           using (_×_; _,_; proj₁; proj₂; map₁)
open import Data.List.Kleene
open import Data.Vec               using (Vec)
open import Induction.WellFounded  using (Acc; acc)
open import Induction.Nat          using (<′-wellFounded)

open import Function

open Homomorphism homo

open import Algebra.Construct.Polynomial.Homomorphism.Lemmas homo
open import Algebra.Construct.Polynomial.Homomorphism.Addition homo
open import Algebra.Construct.Polynomial.Base from
open import Algebra.Construct.Polynomial.Reasoning to
open import Algebra.Operations.Ring.Compact rawRing
open import Algebra.Construct.Polynomial.Semantics homo
open import Algebra.Construct.Polynomial.InjectionIndex
open import Relation.Unary

open import Data.Nat.Induction
open import Induction.WellFounded

reassoc : ∀ {y} x z → x * (y * z) ≈ y * (x * z)
reassoc {y} x z = sym (*-assoc x y z) ⟨ trans ⟩ ((≪* *-comm x y) ⟨ trans ⟩ *-assoc y x z)

mutual
  ⊠-step′-hom : ∀ {n} → (a : Acc _<′_ n) → (xs ys : Poly n) → ∀ ρ → ⟦ ⊠-step′ a xs ys ⟧ ρ ≈ ⟦ xs ⟧ ρ * ⟦ ys ⟧ ρ
  ⊠-step′-hom a (x Π p) = ⊠-step-hom a x p

  ⊠-step-hom : ∀ {i n}
             → (a : Acc _<′_ n)
             → (xs : FlatPoly i)
             → (i≤n : i ≤′ n)
             → (ys : Poly n)
             → ∀ ρ → ⟦ ⊠-step a xs i≤n ys ⟧ ρ ≈ ⟦ xs Π i≤n ⟧ ρ * ⟦ ys ⟧ ρ
  ⊠-step-hom a (Κ x) i≤n = ⊠-Κ-hom a x
  ⊠-step-hom a (Σ xs) i≤n = ⊠-Σ-hom a xs i≤n

  ⊠-Κ-hom : ∀ {n}
          → (a : Acc _<′_ n)
          → ∀ x
          → (ys : Poly n)
          → ∀ ρ
          → ⟦ ⊠-Κ a x ys ⟧ ρ ≈ ⟦ x ⟧ᵣ * ⟦ ys ⟧ ρ
  ⊠-Κ-hom  (acc _) x (Κ y  Π i≤n) ρ = *-homo x y
  ⊠-Κ-hom (acc wf) x (Σ xs Π i≤n) ρ =
    begin
      ⟦ ⊠-Κ-inj (wf _ i≤n) x xs Π↓ i≤n ⟧ ρ
    ≈⟨ Π↓-hom (⊠-Κ-inj (wf _ i≤n) x xs) i≤n ρ ⟩
      Σ?⟦ ⊠-Κ-inj (wf _ i≤n) x xs ⟧ (drop-1 i≤n ρ)
    ≈⟨ ⊠-Κ-inj-hom (wf _ i≤n) x xs (drop-1 i≤n ρ) ⟩
      ⟦ x ⟧ᵣ * Σ⟦ xs ⟧ (drop-1 i≤n ρ)
    ∎

  ⊠-Κ-inj-hom : ∀ {n}
              → (a : Acc _<′_ n)
              → (x : Raw.Carrier)
              → (xs : Coeff n +)
              → ∀ ρ
              → Σ?⟦ ⊠-Κ-inj a x xs ⟧ ρ ≈ ⟦ x ⟧ᵣ * Σ⟦ xs ⟧ ρ
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

  ⊠-Σ-hom : ∀ {i n}
          → (a : Acc _<′_ n)
          → (xs : Coeff i +)
          → (i<n : i <′ n)
          → (ys : Poly n)
          → ∀ ρ
          → ⟦ ⊠-Σ a xs i<n ys ⟧ ρ ≈ Σ⟦ xs ⟧ (drop-1 i<n ρ) * ⟦ ys ⟧ ρ
  ⊠-Σ-hom (acc wf) xs i<n (Σ ys Π j≤n) = ⊠-match-hom (acc wf) (inj-compare i<n j≤n) xs ys
  ⊠-Σ-hom (acc wf) xs i<n (Κ y  Π _) ρ =
    begin
      ⟦ ⊠-Κ-inj (wf _ i<n) y xs Π↓ i<n ⟧ ρ
    ≈⟨ Π↓-hom (⊠-Κ-inj (wf _ i<n) y xs) i<n ρ ⟩
      Σ?⟦ ⊠-Κ-inj (wf _ i<n) y xs ⟧ (drop-1 i<n ρ)
    ≈⟨ ⊠-Κ-inj-hom (wf _ i<n) y xs (drop-1 i<n ρ) ⟩
      ⟦ y ⟧ᵣ * Σ⟦ xs ⟧ (drop-1 i<n ρ)
    ≈⟨ *-comm _ _ ⟩
      Σ⟦ xs ⟧ (drop-1 i<n ρ) * ⟦ y ⟧ᵣ
    ∎

  ⊠-Σ-inj-hom : ∀ {i k}
              → (a : Acc _<′_ k)
              → (i<k : i <′ k)
              → (xs : Coeff i +)
              → (ys : Poly k)
              → ∀ ρ
              → ⟦ ⊠-Σ-inj a i<k xs ys ⟧ ρ ≈ Σ⟦ xs ⟧ (drop-1 i<k ρ) * ⟦ ys ⟧ ρ
  ⊠-Σ-inj-hom (acc wf) i<k x (Σ ys Π j≤k) = ⊠-match-hom (acc wf) (inj-compare i<k j≤k) x ys
  ⊠-Σ-inj-hom (acc wf) i<k x (Κ y Π j≤k) ρ =
    begin
      ⟦ ⊠-Κ-inj (wf _ i<k) y x Π↓ i<k ⟧ ρ
    ≈⟨ Π↓-hom (⊠-Κ-inj (wf _ i<k) y x) i<k ρ ⟩
      Σ?⟦ ⊠-Κ-inj (wf _ i<k) y x ⟧ (drop-1 i<k ρ)
    ≈⟨ ⊠-Κ-inj-hom (wf _ i<k) y x (drop-1 i<k ρ) ⟩
      ⟦ y ⟧ᵣ * Σ⟦ x ⟧ (drop-1 i<k ρ)
    ≈⟨ *-comm _ _ ⟩
      Σ⟦ x ⟧ (drop-1 i<k ρ) * ⟦ y ⟧ᵣ
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
              ≈ Σ⟦ xs ⟧ (drop-1 i<n Ρ) * Σ⟦ ys ⟧ (drop-1 j<n Ρ)
  ⊠-match-hom {j = j} (acc wf) (inj-lt i≤j-1 j≤n) xs ys Ρ′ =
    let (ρ , Ρ) = drop-1 j≤n Ρ′
        xs′ = Σ⟦ xs ⟧ (drop-1 (≤′-trans (≤′-step i≤j-1) j≤n) Ρ′)
    in
    begin
      ⟦ poly-map ( (⊠-Σ-inj (wf _ j≤n) i≤j-1 xs)) ys Π↓ j≤n ⟧ Ρ′
    ≈⟨ Π↓-hom (poly-map ( (⊠-Σ-inj (wf _ j≤n) i≤j-1 xs)) ys) j≤n Ρ′ ⟩
      Σ?⟦ poly-map ( (⊠-Σ-inj (wf _ j≤n) i≤j-1 xs)) ys ⟧ (ρ , Ρ)
    ≈⟨ poly-mapR ρ Ρ (⊠-Σ-inj (wf _ j≤n) i≤j-1 xs)
                     (_ *_)
                     (*-cong refl)
                     reassoc
                     (distribˡ _)
                     (λ y → ⊠-Σ-inj-hom (wf _ j≤n) i≤j-1 xs y _)
                     (zeroʳ _) ys ⟩
       Σ⟦ xs ⟧ (drop-1 i≤j-1 Ρ) * Σ⟦ ys ⟧ (ρ , Ρ)
    ≈⟨ ≪* trans-join-coeffs-hom i≤j-1 j≤n xs Ρ′ ⟩
      xs′ * Σ⟦ ys ⟧ (ρ , Ρ)
    ∎
  ⊠-match-hom (acc wf) (inj-gt i≤n j≤i-1) xs ys Ρ′ =
    let (ρ , Ρ) = drop-1 i≤n Ρ′
        ys′ = Σ⟦ ys ⟧ (drop-1 (≤′-step j≤i-1 ⟨ ≤′-trans ⟩ i≤n) Ρ′)
    in
    begin
      ⟦ poly-map ( (⊠-Σ-inj (wf _ i≤n) j≤i-1 ys)) xs Π↓ i≤n ⟧ Ρ′
    ≈⟨ Π↓-hom (poly-map ( (⊠-Σ-inj (wf _ i≤n) j≤i-1 ys)) xs) i≤n Ρ′ ⟩
      Σ?⟦ poly-map ( (⊠-Σ-inj (wf _ i≤n) j≤i-1 ys)) xs ⟧ (ρ , Ρ)
    ≈⟨ poly-mapR ρ Ρ (⊠-Σ-inj (wf _ i≤n) j≤i-1 ys)
                     (_ *_)
                     (*-cong refl)
                     reassoc
                     (distribˡ _)
                     (λ x → ⊠-Σ-inj-hom (wf _ i≤n) j≤i-1 ys x _)
                     (zeroʳ _) xs ⟩
      Σ⟦ ys ⟧ (drop-1 j≤i-1 Ρ) * Σ⟦ xs ⟧ (ρ , Ρ)
    ≈⟨ ≪* trans-join-coeffs-hom j≤i-1 i≤n ys Ρ′ ⟩
      ys′ * Σ⟦ xs ⟧ (ρ , Ρ)
    ≈⟨ *-comm ys′ _ ⟩
      Σ⟦ xs ⟧ (ρ , Ρ) * ys′
    ∎
  ⊠-match-hom (acc wf) (inj-eq ij≤n) xs ys Ρ =
    begin
      ⟦ ⊠-coeffs (wf _ ij≤n) xs ys Π↓ ij≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊠-coeffs (wf _ ij≤n) xs ys) ij≤n Ρ ⟩
      Σ?⟦ ⊠-coeffs (wf _ ij≤n) xs ys ⟧ (drop-1 ij≤n Ρ)
    ≈⟨ ⊠-coeffs-hom (wf _ ij≤n) xs ys (drop-1 ij≤n Ρ) ⟩
      Σ⟦ xs ⟧ (drop-1 ij≤n Ρ) * Σ⟦ ys ⟧ (drop-1 ij≤n Ρ)
    ∎

  ⊠-coeffs-hom : ∀ {n}
               → (a : Acc _<′_ n)
               → (xs : Coeff n +)
               → (ys : Coeff n +)
               → ∀ ρ → Σ?⟦ ⊠-coeffs a xs ys ⟧ ρ ≈ Σ⟦ xs ⟧ ρ * Σ⟦ ys ⟧ ρ
  ⊠-coeffs-hom a xs (y ≠0 Δ j & []) (ρ , Ρ) =
    begin
      Σ?⟦ poly-map (⊠-step′ a y) xs ⍓* j ⟧ (ρ , Ρ)
    ≈⟨ sym (pow′-hom j (poly-map (⊠-step′ a y) xs) ρ Ρ) ⟩
      Σ?⟦ poly-map (⊠-step′ a y) xs ⟧ (ρ , Ρ) *⟨ ρ ⟩^ j
    ≈⟨ pow-mul-cong (poly-mapR ρ Ρ (⊠-step′ a y) (⟦ y ⟧ Ρ *_) (*-cong refl) reassoc (distribˡ _) (λ z → ⊠-step′-hom a y z Ρ) (zeroʳ _) xs) ρ j ⟩
      (⟦ y ⟧ Ρ * Σ⟦ xs ⟧ (ρ , Ρ)) *⟨ ρ ⟩^ j
    ≈⟨ pow-opt _ ρ j ⟩
      (ρ ^ j) * (⟦ y ⟧ Ρ * Σ⟦ xs ⟧ (ρ , Ρ))
    ≈⟨ sym (*-assoc _ _ _) ⟩
      (ρ ^ j) * ⟦ y ⟧ Ρ * Σ⟦ xs ⟧ (ρ , Ρ)
    ≈⟨ *-comm _ _ ⟩
      Σ⟦ xs ⟧ (ρ , Ρ) * ((ρ ^ j) * ⟦ y ⟧ Ρ)
    ≈⟨ *≫ sym (pow-opt _ ρ j) ⟩
      Σ⟦ xs ⟧ (ρ , Ρ) * (⟦ y ⟧ Ρ *⟨ ρ ⟩^ j)
    ∎
  ⊠-coeffs-hom a xs (y ≠0 Δ j & ∹ ys) (ρ , Ρ) =
    let xs′ = Σ⟦ xs ⟧ (ρ , Ρ)
        y′  = ⟦ y ⟧ Ρ
        ys′ = Σ⟦ ys ⟧ (ρ , Ρ)
    in
    begin
      Σ?⟦ para (⊠-cons a y ys) xs ⍓* j ⟧ (ρ , Ρ)
    ≈⟨ sym (pow′-hom j (para (⊠-cons a y ys) xs) ρ Ρ) ⟨ trans ⟩ pow-opt _ ρ j ⟩
      ρ ^ j * Σ?⟦ para (⊠-cons a y ys) xs ⟧ (ρ , Ρ)
    ≈⟨ *≫ ⊠-cons-hom a y ys xs ρ Ρ ⟩
     ρ ^ j * (xs′ * (ρ * ys′ + y′))
    ≈⟨ sym (*-assoc _ _ _) ⟨ trans ⟩ (≪* *-comm _ _) ⟨ trans ⟩ *-assoc _ _ _ ⟨ trans ⟩ (*≫ sym (pow-opt _ ρ j))⟩
      xs′ * ((ρ * ys′ + y′) *⟨ ρ ⟩^ j)
    ∎

  ⊠-cons-hom : ∀ {n}
             → (a : Acc _<′_ n)
             → (y : Poly n)
             → (ys : Coeff n +)
             → (xs : Coeff n +)
             → (ρ : Carrier)
             → (Ρ : Vec Carrier n)
             → Σ?⟦ para (⊠-cons a y ys) xs ⟧ (ρ , Ρ)
             ≈ Σ⟦ xs ⟧ (ρ , Ρ) * (ρ * Σ⟦ ys ⟧ (ρ , Ρ) + ⟦ y ⟧ Ρ)
  -- ⊠-cons-hom a y [] xs ρ Ρ = {!!}
  ⊠-cons-hom a y ys xs ρ Ρ = poly-foldR ρ Ρ (⊠-cons a y ys) (flip _*_ (ρ * Σ⟦ ys ⟧ (ρ , Ρ) + ⟦ y ⟧ Ρ)) (flip *-cong refl) (λ x y → sym (*-assoc x y _)) step (zeroˡ _) xs
    where
    step = λ { (z Π j≤n) {ys₁} zs ys≋zs →
      let x′  = ⟦ z Π j≤n ⟧ Ρ
          xs′ = Σ?⟦ zs ⟧ (ρ , Ρ)
          y′  = ⟦ y ⟧ Ρ
          ys′ = Σ⟦ ys ⟧ (ρ , Ρ)
          step = λ y → ⊠-step-hom a z j≤n y Ρ
      in
      begin
        ρ * Σ?⟦ ⊞-coeffs (poly-map ( (⊠-step a z j≤n)) ys) ys₁ ⟧ (ρ , Ρ) + ⟦ ⊠-step a z j≤n y ⟧ Ρ
      ≈⟨ (*≫ ⊞-coeffs-hom (poly-map (⊠-step a z j≤n) ys) _ (ρ , Ρ)) ⟨ +-cong ⟩ ⊠-step-hom a z j≤n y Ρ ⟩
        ρ * (Σ?⟦ poly-map (⊠-step a z j≤n) ys ⟧ (ρ , Ρ) + Σ?⟦ ys₁ ⟧ (ρ , Ρ)) + x′ * y′
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

⊠-hom : ∀ {n}
      → (xs : Poly n)
      → (ys : Poly n)
      → ∀ ρ → ⟦ xs ⊠ ys ⟧ ρ ≈ ⟦ xs ⟧ ρ * ⟦ ys ⟧ ρ
⊠-hom (xs Π i≤n) = ⊠-step-hom (<′-wellFounded _) xs i≤n
