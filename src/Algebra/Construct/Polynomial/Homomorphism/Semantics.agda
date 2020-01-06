{-# OPTIONS --without-K --safe #-}

open import Algebra.Construct.Polynomial.Parameters

module Algebra.Construct.Polynomial.Homomorphism.Semantics
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Product        using (_,_)
open import Data.Vec as Vec     using (Vec)
open import Data.Fin            using (Fin)
open import Data.Fin.Properties using (space≤′n)
open import Data.List.Kleene
open import Function

open Homomorphism homo

open import Algebra.Construct.Polynomial.Homomorphism.Lemmas homo
open import Algebra.Construct.Polynomial.Base (Homomorphism.from homo)
open import Algebra.Construct.Polynomial.Reasoning (Homomorphism.to homo)
open import Algebra.Construct.Polynomial.Semantics homo

open import Algebra.Operations.Ring rawRing

κ-hom : ∀ {n} (x : Raw.Carrier) (Ρ : Vec Carrier n) → ⟦ κ x ⟧ Ρ ≈ ⟦ x ⟧ᵣ
κ-hom x _ = refl

ι-hom : ∀ {n} (i : Fin n) (Ρ : Vec Carrier n) → ⟦ ι i ⟧ Ρ ≈ Vec.lookup Ρ i
ι-hom i Ρ′ =
  let (ρ , Ρ) = drop-1 (space≤′n i) Ρ′
  in
  begin
    ⟦ (κ Raw.1# Δ 1 ∷↓ []) ⊐↓ space≤′n i ⟧ Ρ′
  ≈⟨ ⊐↓-hom (κ Raw.1# Δ 1 ∷↓ []) (space≤′n i) Ρ′ ⟩
    ⅀?⟦ κ Raw.1# Δ 1 ∷↓ [] ⟧ (ρ , Ρ)
  ≈⟨ ∷↓-hom-s (κ Raw.1#) 0 [] ρ Ρ  ⟩
    ρ * ⟦ κ Raw.1# ⟧ Ρ
  ≈⟨ *≫ 1-homo ⟩
    ρ * 1#
  ≈⟨ *-identityʳ ρ ⟩
    ρ
  ≡⟨ drop-1⇒lookup i Ρ′ ⟩
    Vec.lookup Ρ′ i
  ∎
