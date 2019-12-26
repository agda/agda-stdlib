{-# OPTIONS --without-K --safe #-}

module Algebra.Solver.Ring.Simple.AlmostCommutativeRing.Instances where

{-
open import Algebra.Solver.Ring.Simple.AlmostCommutativeRing
open import Level using (0ℓ)
open import Agda.Builtin.Reflection

module Nat where
  open import Data.Nat using (zero; suc)
  open import Relation.Binary.PropositionalEquality using (refl)
  open import Data.Nat.Properties using (*-+-commutativeSemiring)
  open import Data.Maybe using (just; nothing)

  ring : AlmostCommutativeRing 0ℓ 0ℓ
  ring =
    fromCommutativeSemiring
      *-+-commutativeSemiring
      λ { zero → just refl; _ → nothing }

  module Reflection where
    open import Algebra.Solver.Ring.Simple.Reflection using (solveOver-macro)
    open import Data.Unit using (⊤)

    macro
      ∀⟨_⟩ : Term → Term → TC ⊤
      ∀⟨ n ⟩ = solveOver-macro n (quote ring)

module Int where
  open import Data.Nat using (zero)
  open import Data.Integer using (+_)
  open import Data.Integer.Properties using(+-*-commutativeRing)
  open import Data.Maybe using (just; nothing)
  open import Relation.Binary.PropositionalEquality using (refl)

  ring : AlmostCommutativeRing 0ℓ 0ℓ
  ring =
    fromCommutativeRing
      +-*-commutativeRing
      λ { (+ zero) → just refl; _ → nothing }

  module Reflection where
    open import Polynomial.Simple.Reflection using (solveOver-macro)
    open import Data.Unit using (⊤)

    macro
      ∀⟨_⟩ : Term → Term → TC ⊤
      ∀⟨ n ⟩ = solveOver-macro n (quote ring)
-}
