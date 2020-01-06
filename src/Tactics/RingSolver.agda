{-# OPTIONS --without-K --safe #-}

open import Algebra.Construct.Polynomial.Parameters

module Tactics.RingSolver
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Algebra.Solver.Ring.AlmostCommutativeRing
import Algebra.Construct.Polynomial.Homomorphism homo as Hom
open import Algebra.Construct.Polynomial.Semantics homo
  renaming (⟦_⟧ to ⟦_⟧ₚ)
open import Data.Vec as Vec using (Vec)
open import Function

open import Tactics.RingSolver.Core.Expression public

open Homomorphism homo
open Eval rawRing ⟦_⟧ᵣ

open import Algebra.Construct.Polynomial.Base from
  using (Poly; _⊞_; _⊠_; ⊟_; _⊡_; κ; ι)

norm : ∀ {n} → Expr Raw.Carrier n → Poly n
norm (Κ x)   = κ x
norm (Ι x)   = ι x
norm (x ⊕ y) = norm x ⊞ norm y
norm (x ⊗ y) = norm x ⊠ norm y
norm (x ⊛ i) = norm x ⊡ i
norm (⊝ x)   = ⊟ norm x

⟦_⇓⟧ : ∀ {n} → Expr Raw.Carrier n → Vec Carrier n → Carrier
⟦ x ⇓⟧ = ⟦ norm x ⟧ₚ

correct : ∀ {n} (e : Expr Raw.Carrier n) ρ → ⟦ e ⇓⟧ ρ ≈ ⟦ e ⟧ ρ
correct (Κ x)   ρ = Hom.κ-hom x ρ
correct (Ι x)   ρ = Hom.ι-hom x ρ
correct (x ⊕ y) ρ = Hom.⊞-hom (norm x) (norm y) ρ ⟨ trans ⟩ (correct x ρ ⟨ +-cong ⟩ correct y ρ)
correct (x ⊗ y) ρ = Hom.⊠-hom (norm x) (norm y) ρ ⟨ trans ⟩ (correct x ρ ⟨ *-cong ⟩ correct y ρ)
correct (x ⊛ i) ρ = Hom.⊡-hom (norm x) i ρ        ⟨ trans ⟩ (Hom.pow-cong i (correct x ρ))
correct (⊝ x)   ρ = Hom.⊟-hom (norm x) ρ          ⟨ trans ⟩ -‿cong (correct x ρ)

open import Relation.Binary.Reflection setoid Ι ⟦_⟧ ⟦_⇓⟧ correct public
