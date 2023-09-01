{-# OPTIONS --cubical-compatible --safe #-}

module README.Tactic.Cong where

open import Data.Nat
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Preorder as PR

open import Tactic.Cong using (cong!)

----------------------------------------------------------------------
-- Usage
----------------------------------------------------------------------

-- When performing large equational reasoning proofs, it's quite
-- common to have to construct sophisticated lambdas to pass
-- into 'cong'. This can be extremely tedious, and can bog down
-- large proofs in piles of boilerplate. The 'cong!' tactic
-- simplifies this process by synthesizing the appropriate call
-- to 'cong' by inspecting both sides of the goal.
--
-- This is best demonstrated with a small example. Consider
-- the following proof:

verbose-example : ∀ m n → m ≡ n → suc (suc (m + 0)) + m ≡ suc (suc n) + (n + 0)
verbose-example m n eq =
  let open Eq.≡-Reasoning in
  begin
    suc (suc (m + 0)) + m
  ≡⟨ cong (λ ϕ → suc (suc (ϕ + m))) (+-identityʳ m) ⟩
    suc (suc m) + m
  ≡⟨ cong (λ ϕ → suc (suc (ϕ + ϕ))) eq ⟩
    suc (suc n) + n
  ≡˘⟨ cong (λ ϕ → suc (suc (n + ϕ))) (+-identityʳ n) ⟩
    suc (suc n) + (n + 0)
  ∎

-- The calls to 'cong' add a lot of boilerplate, and also
-- clutter up the proof, making it more difficult to read.
-- We can simplify this by using 'cong!' to deduce those
-- lambdas for us.

succinct-example : ∀ m n → m ≡ n → suc (suc (m + 0)) + m ≡ suc (suc n) + (n + 0)
succinct-example m n eq =
  let open Eq.≡-Reasoning in
  begin
    suc (suc (m + 0)) + m
  ≡⟨ cong! (+-identityʳ m) ⟩
    suc (suc m) + m
  ≡⟨ cong! eq ⟩
    suc (suc n) + n
  ≡˘⟨ cong! (+-identityʳ n) ⟩
    suc (suc n) + (n + 0)
  ∎

----------------------------------------------------------------------
-- Limitations
----------------------------------------------------------------------

-- The 'cong!' tactic can handle simple cases, but will
-- struggle when presented with equality proofs like
-- 'm + n ≡ n + m' or 'm + (n + o) ≡ (m + n) + o'.
--
-- The reason behind this is that this tactic operates by simple
-- anti-unification; it examines both sides of the equality goal
-- to deduce where to generalize. When presented with two sides
-- of an equality like 'm + n ≡ n + m', it will anti-unify to
-- 'ϕ + ϕ', which is too specific.

----------------------------------------------------------------------
-- Unit Tests
----------------------------------------------------------------------

module LiteralTests
  (assumption : 48 ≡ 42)
  (f : ℕ → ℕ → ℕ → ℕ)
  where

  test₁ : 40 + 2 ≡ 42
  test₁ = cong! refl

  test₂ : 48 ≡ 42 → 42 ≡ 48
  test₂ eq = cong! (sym eq)

  test₃ : (f : ℕ → ℕ) → f 48 ≡ f 42
  test₃ f = cong! assumption

  test₄ : (f : ℕ → ℕ → ℕ) → f 48 48 ≡ f 42 42
  test₄ f = cong! assumption

  test₅ : f 48 45 48 ≡ f 42 45 42
  test₅ = cong! assumption

module LambdaTests
  (assumption : 48 ≡ 42)
  where

  test₁ : (λ x → x + 48) ≡ (λ x → x + 42)
  test₁ = cong! assumption

  test₂ : (λ x y z → x + (y + 48 + z)) ≡ (λ x y z → x + (y + 42 + z))
  test₂ = cong! assumption

module HigherOrderTests
  (f g : ℕ → ℕ)
  where

  test₁ : f ≡ g → ∀ n → f n ≡ g n
  test₁ eq n = cong! eq

  test₂ : f ≡ g → ∀ n → f (f (f n)) ≡ g (g (g n))
  test₂ eq n = cong! eq

module EquationalReasoningTests where

  test₁ : ∀ m n → m ≡ n → suc (suc (m + 0)) + m ≡ suc (suc n) + (n + 0)
  test₁ m n eq =
    let open Eq.≡-Reasoning in
    begin
      suc (suc (m + 0)) + m
    ≡⟨ cong! (+-identityʳ m) ⟩
      suc (suc m) + m
    ≡⟨ cong! eq ⟩
      suc (suc n) + n
    ≡˘⟨ cong! (+-identityʳ n) ⟩
      suc (suc n) + (n + 0)
    ∎

  test₂ : ∀ m n → m ≡ n → suc (m + m) ≤ suc (suc (n + n))
  test₂ m n eq =
    let open PR ≤-preorder in
    begin
      suc (m + m)
    ≡⟨ cong! eq ⟩
      suc (n + n)
    ∼⟨ ≤-step ≤-refl ⟩
      suc (suc (n + n))
    ∎
