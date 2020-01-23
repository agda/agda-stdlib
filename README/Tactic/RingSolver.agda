------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples showing how the reflective ring solver may be used.
------------------------------------------------------------------------

module README.Tactic.RingSolver where

-- You can ignore this bit! We're just overloading the literals Agda uses for
-- numbers. This bit isn't necessary if you're just using Nats, or if you
-- construct your type directly. We only really do it here so that we can use
-- different numeric types in the same file.

open import Agda.Builtin.FromNat
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
import Data.Nat.Literals as ℕ
import Data.Integer.Literals as ℤ

instance
  numberNat : Number ℕ
  numberNat = ℕ.number

instance
  numberInt : Number ℤ
  numberInt = ℤ.number

------------------------------------------------------------------------------
-- Imports!

open import Data.List as List using (List; _∷_; [])
open import Function
open import Relation.Binary.PropositionalEquality as ≡
  using (subst; _≡_; module ≡-Reasoning)
open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (⊤; tt)

open import Tactic.RingSolver.Core.AlmostCommutativeRing using (AlmostCommutativeRing)

------------------------------------------------------------------------------
-- Integer examples
------------------------------------------------------------------------------

module IntegerExamples where
  open import Data.Integer.Tactic.RingSolver

  open AlmostCommutativeRing ring

  -- Everything is automatic: you just ask Agda to solve it and it does!
  lemma₁ : ∀ x y → x + y * 1 + 3 ≈ 3 + 1 + y + x + - 1
  lemma₁ = solve-∀

  lemma₂ : ∀ x y → (x + y) ^ 2 ≈ x ^ 2 + 2 * x * y + y ^ 2
  lemma₂ = solve-∀

  -- It can interact with manual proofs as well.
  lemma₃ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
  lemma₃ x y = begin
    x + y * 1 + 3 ≡⟨ +-comm x (y * 1) ⟨ +-cong ⟩ refl ⟩
    y * 1 + x + 3 ≡⟨ solve (x ∷ y ∷ []) ⟩
    3 + y + x     ≡⟨⟩
    2 + 1 + y + x ∎
    where open ≡-Reasoning

------------------------------------------------------------------------------
-- Natural examples
------------------------------------------------------------------------------

module NaturalExamples where
  open import Data.Nat.Tactic.RingSolver

  open AlmostCommutativeRing ring

  -- The solver is flexible enough to work with ℕ (even though it asks
  -- for rings!)
  lemma₁ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
  lemma₁ = solve-∀

------------------------------------------------------------------------------
-- Checking invariants
------------------------------------------------------------------------------
-- The solver makes it easy to prove invariants, without having to rewrite
-- proof code every time something changes in the data structure.

module _ {a} {A : Set a} (_≤_ : A → A → Bool) where
  open import Data.Nat.Tactic.RingSolver
  open AlmostCommutativeRing ring

  -- A Skew Heap, indexed by its size.
  data Tree : ℕ → Set a where
    leaf : Tree 0
    node : ∀ {n m} → A → Tree n → Tree m → Tree (1 + n + m)

  -- A substitution operator, to clean things up.
  infixr 1 _⇒_
  _⇒_ : ∀ {n} → Tree n → ∀ {m} → n ≈ m → Tree m
  x ⇒ n≈m  = subst Tree n≈m x

  open ≡-Reasoning

  _∪_ : ∀ {n m} → Tree n → Tree m → Tree (n + m)
  leaf                 ∪ ys                   = ys
  node {a} {b} x xl xr ∪ leaf                 =
    node x xl xr ⇒ solve (a ∷ b ∷ [])
  node {a} {b} x xl xr ∪ node {c} {d} y yl yr =
      if x ≤ y
        then node x (node y yl yr ∪ xr) xl ⇒ begin
          1 + (1 + c + d + b) + a ≡⟨ solve (a ∷ b ∷ c ∷ d ∷ []) ⟩
          1 + a + b + (1 + c + d) ∎
        else node y (node x xl xr ∪ yr) yl ⇒ begin
          1 + (1 + a + b + d) + c ≡⟨ solve (a ∷ b ∷ c ∷ d ∷ []) ⟩
          1 + a + b + (1 + c + d) ∎
