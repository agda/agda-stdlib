------------------------------------------------------------------------
-- The Agda standard library
--
-- Homomorphism proofs for constants over polynomials
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Tactic.RingSolver.Core.Polynomial.Parameters

module Tactic.RingSolver.Core.Polynomial.Homomorphism.Constants
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open Homomorphism homo

open import Data.Vec.Base using (Vec)

open import Tactic.RingSolver.Core.Polynomial.Base (Homomorphism.from homo)
open import Tactic.RingSolver.Core.Polynomial.Semantics homo

κ-hom : ∀ {n} (x : Raw.Carrier) (Ρ : Vec Carrier n) → ⟦ κ x ⟧ Ρ ≈ ⟦ x ⟧ᵣ
κ-hom x _ = refl
