------------------------------------------------------------------------
-- The Agda standard library
--
-- Some specialised instances of the ring solver
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Tactic.RingSolver.Instances where

open import Agda.Builtin.Reflection

open import Tactic.RingSolver.Core.AlmostCommutativeRing
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Nat using (zero; suc)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (⊤)
open import Tactic.RingSolver using (solveOver-macro)

module Nat where
  open import Data.Nat.Properties using (*-+-commutativeSemiring)

  ring : AlmostCommutativeRing 0ℓ 0ℓ
  ring = fromCommutativeSemiring *-+-commutativeSemiring
    λ { zero → just refl; _ → nothing }

  macro
    ∀⟨_⟩ : Term → Term → TC ⊤
    ∀⟨ n ⟩ = solveOver-macro n (quote ring)

module Int where
  open import Data.Integer using (+_)
  open import Data.Integer.Properties using(+-*-commutativeRing)

  ring : AlmostCommutativeRing 0ℓ 0ℓ
  ring = fromCommutativeRing +-*-commutativeRing
    λ { (+ zero) → just refl; _ → nothing }

  macro
    ∀⟨_⟩ : Term → Term → TC ⊤
    ∀⟨ n ⟩ = solveOver-macro n (quote ring)
