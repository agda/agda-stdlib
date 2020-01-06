------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples showing how the reflective ring solver may be used.
------------------------------------------------------------------------

module README.Tactics.RingSolver where

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
open import Relation.Binary.PropositionalEquality as ≡ using (subst; _≡_)
open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (⊤; tt)

open import Tactics.RingSolver.Core.AlmostCommutativeRing using (AlmostCommutativeRing)
open import Tactics.RingSolver.Instances
open import Tactics.RingSolver

------------------------------------------------------------------------------
-- Integer examples
------------------------------------------------------------------------------

module IntegerExamples where
  open AlmostCommutativeRing Int.ring
  -- Everything is automatic: you just ask Agda to solve it and it does!
  lemma₁ : ∀ x y → x + y * 1 + 3 ≈ 3 + 1 + y + x + - 1
  lemma₁ = solve Int.ring

  lemma₂ : ∀ x y → (x + y) ^ 2 ≈ x ^ 2 + 2 * x * y + y ^ 2
  lemma₂ = solve Int.ring

  open import Relation.Binary.Reasoning.Inference setoid

  -- It can interact with manual proofs as well.
  lemma₃ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
  lemma₃ x y = begin
    x + y * 1 + 3 ≈⟨ +-comm x (y * 1) ⟨ +-cong ⟩ refl ⟩
    y * 1 + x + 3 ≈⟨ solveOver (x ∷ y ∷ []) Int.ring ⟩
    3 + y + x     ≡⟨⟩
    2 + 1 + y + x ∎

------------------------------------------------------------------------------
-- Natural examples
------------------------------------------------------------------------------

module NaturalExamples where

  open AlmostCommutativeRing Nat.ring

  -- The solver is flexible enough to work with ℕ (even though it asks
  -- for rings!)
  lemma₁ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
  lemma₁ = solve Nat.ring


------------------------------------------------------------------------------
-- Checking invariants
------------------------------------------------------------------------------
-- The solver makes it easy to prove invariants, without having to rewrite
-- proof code every time something changes in the data structure.

module _ {a} {A : Set a} (_≤_ : A → A → Bool) where

  open AlmostCommutativeRing Nat.ring

  -- A Skew Heap, indexed by its size.
  data Tree : ℕ → Set a where
    leaf : Tree 0
    node : ∀ {n m} → A → Tree n → Tree m → Tree (n + m + 1)

  -- A substitution operator, to clean things up.
  _⇒_ : ∀ {n} → Tree n → ∀ {m} → n ≈ m → Tree m
  x ⇒ n≈m  = subst Tree n≈m x
{-
  _∪_ : ∀ {n m} → Tree n → Tree m → Tree (n + m)
  leaf                 ∪ ys                   = ys
  node {a} {b} x xl xr ∪ leaf                 =
    node x xl xr ⇒ solveOver (a ∷ b ∷ []) Nat.ring
  node {a} {b} x xl xr ∪ node {c} {d} y yl yr = if x ≤ y
    then node x (node y yl yr ∪ xr) xl
      ⇒ (solveOver (a ∷ b ∷ c ∷ d ∷ []) Nat.ring)
    else (node y (node x xl xr ∪ yr) yl
      ⇒ (solveOver (a ∷ b ∷ c ∷ d ∷ []) Nat.ring))
-}
