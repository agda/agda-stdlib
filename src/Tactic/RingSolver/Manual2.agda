------------------------------------------------------------------------
-- The Agda standard library
--
-- An implementation of the ring solver that requires you to manually
-- pass the equation you wish to solve.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Tactic.RingSolver.Core.Polynomial.Parameters

module Tactic.RingSolver.Manual2
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Data.Vec using (Vec)
open import Function.Base using (_⟨_⟩_)

open import Tactic.RingSolver.Core.Expression public
import Tactic.RingSolver.Core.Polynomial.Homomorphism homo as Hom
open import Tactic.RingSolver.Core.Polynomial.Semantics homo
  renaming (⟦_⟧ to ⟦_⟧ₚ)

open Homomorphism homo
open Eval rawRing ⟦_⟧ᵣ

open import Tactic.RingSolver.Core.Polynomial.Base from
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
