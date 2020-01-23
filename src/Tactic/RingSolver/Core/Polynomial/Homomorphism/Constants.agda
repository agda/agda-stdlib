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

open import Data.Product        using (_,_)
open import Data.Vec as Vec     using (Vec)
open import Data.Fin            using (Fin)
open import Data.Fin.Properties using (space≤′n)
open import Data.List.Kleene
open import Function

open Homomorphism homo

open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Lemmas homo
open import Tactic.RingSolver.Core.Polynomial.Base (Homomorphism.from homo)
open import Tactic.RingSolver.Core.Polynomial.Reasoning (Homomorphism.to homo)
open import Tactic.RingSolver.Core.Polynomial.Semantics homo

open import Algebra.Operations.Ring rawRing

κ-hom : ∀ {n} (x : Raw.Carrier) (Ρ : Vec Carrier n) → ⟦ κ x ⟧ Ρ ≈ ⟦ x ⟧ᵣ
κ-hom x _ = refl
