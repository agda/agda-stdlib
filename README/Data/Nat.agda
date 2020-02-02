------------------------------------------------------------------------
-- The Agda standard library
--
-- Some examples showing where the natural numbers and some related
-- operations and properties are defined, and how they can be used
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README.Data.Nat where

-- The natural numbers and various arithmetic operations are defined
-- in Data.Nat.

open import Data.Nat using (ℕ; _+_; _*_)

-- _*_ has precedence 7 over precedence 6 of _+_
-- precedence of both defined in module Agda.Builtin.Nat
ex₁ : ℕ
ex₁ = 1 + 3 * 4

-- Propositional equality and some related properties can be found
-- in Relation.Binary.PropositionalEquality.

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

ex₂ : 3 + 5 ≡ 2 * 4
ex₂ = refl

-- Data.Nat.Properties contains a number of properties about natural
-- numbers.

open import Data.Nat.Properties using (*-comm; +-identityʳ)

ex₃ : ∀ m n → m * n ≡ n * m
ex₃ m n = *-comm m n

-- The module ≡-Reasoning in Relation.Binary.PropositionalEquality
-- provides some combinators for equational reasoning.

open Relation.Binary.PropositionalEquality using (cong; module ≡-Reasoning)

ex₄ : ∀ m n → m * (n + 0) ≡ n * m
ex₄ m n = begin
  m * (n + 0)  ≡⟨ cong (_*_ m) (+-identityʳ n) ⟩
  m * n        ≡⟨ *-comm m n ⟩
  n * m        ∎
  where open ≡-Reasoning

-- The module SemiringSolver in Data.Nat.Solver contains a solver
-- for natural number equalities involving variables, constants, _+_
-- and _*_.

open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)

ex₅ : ∀ m n → m * (n + 0) ≡ n * m
ex₅ = solve 2 (λ m n → m :* (n :+ con 0)  :=  n :* m) refl
