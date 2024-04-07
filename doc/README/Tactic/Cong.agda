{-# OPTIONS --cubical-compatible --safe #-}

module README.Tactic.Cong where

open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; module ≡-Reasoning)

open import Tactic.Cong using (cong! ; ⌞_⌟)

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
  let open ≡-Reasoning in
  begin
    suc (suc (m + 0)) + m
  ≡⟨ cong (λ ϕ → suc (suc (ϕ + m))) (+-identityʳ m) ⟩
    suc (suc m) + m
  ≡⟨ cong (λ ϕ → suc (suc (ϕ + ϕ))) eq ⟩
    suc (suc n) + n
  ≡⟨ cong (λ ϕ → suc (suc (n + ϕ))) (+-identityʳ n) ⟨
    suc (suc n) + (n + 0)
  ∎

-- The calls to 'cong' add a lot of boilerplate, and also
-- clutter up the proof, making it more difficult to read.
-- We can simplify this by using 'cong!' to deduce those
-- lambdas for us.

succinct-example : ∀ m n → m ≡ n → suc (suc (m + 0)) + m ≡ suc (suc n) + (n + 0)
succinct-example m n eq =
  let open ≡-Reasoning in
  begin
    suc (suc (m + 0)) + m
  ≡⟨ cong! (+-identityʳ m) ⟩
    suc (suc m) + m
  ≡⟨ cong! eq ⟩
    suc (suc n) + n
  ≡⟨ cong! (+-identityʳ n) ⟨
    suc (suc n) + (n + 0)
  ∎

----------------------------------------------------------------------
-- Explicit markings
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
--
-- In cases like these, you may explicitly mark the subterms to
-- be generalized by wrapping them in the marker function, ⌞_⌟.

marker-example₁ : ∀ m n o p → m + n + (o + p) ≡ n + m + (p + o)
marker-example₁ m n o p =
  let open ≡-Reasoning in
  begin
    ⌞ m + n ⌟ + (o + p)
  ≡⟨ cong! (+-comm m n) ⟩
    n + m + ⌞ o + p ⌟
  ≡⟨ cong! (+-comm p o) ⟨
    n + m + (p + o)
  ∎

marker-example₂ : ∀ m n → m + n + (m + n) ≡ n + m + (n + m)
marker-example₂ m n =
  let open ≤-Reasoning in
  begin-equality
    ⌞ m + n ⌟ + ⌞ m + n ⌟
  ≡⟨ cong! (+-comm m n) ⟩
    n + m + (n + m)
  ∎

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
    let open ≡-Reasoning in
    begin
      suc (suc (m + 0)) + m
    ≡⟨ cong! (+-identityʳ m) ⟩
      suc (suc m) + m
    ≡⟨ cong! eq ⟩
      suc (suc n) + n
    ≡⟨ cong! (+-identityʳ n) ⟨
      suc (suc n) + (n + 0)
    ∎

  test₂ : ∀ m n → m ≡ n → suc (m + m) ≤ suc (suc (n + n))
  test₂ m n eq =
    let open ≤-Reasoning in
    begin
      suc (m + m)
    ≡⟨ cong! eq ⟩
      suc (n + n)
    ≤⟨ n≤1+n _ ⟩
      suc (suc (n + n))
    ∎

module MetaTests where

  test₁ : ∀ m n o → .⦃ _ : NonZero o ⦄ → (m + n) / o ≡ (n + m) / o
  test₁ m n o =
    let open ≤-Reasoning in
    begin-equality
      ⌞ m + n ⌟ / o
     ≡⟨ cong! (+-comm m n) ⟩
      (n + m) / o
    ∎

  test₂ : ∀ m n o p q r → .⦃ _ : NonZero o ⦄ → .⦃ _ : NonZero p ⦄ →
          .⦃ _ : NonZero q ⦄ → p ≡ q ^ r → (m + n) % o % p ≡ (n + m) % o % p
  test₂ m n o p q r eq =
    let
      open ≤-Reasoning
      instance q^r≢0 = m^n≢0 q r
    in
    begin-equality
      (m + n) % o % p
     ≡⟨ %-congʳ eq ⟩
      ⌞ m + n ⌟ % o % q ^ r
     ≡⟨ cong! (+-comm m n) ⟩
      ⌞ n + m ⌟ % o % q ^ r
     ≡⟨ cong! (+-comm m n) ⟨
      ⌞ m + n ⌟ % o % q ^ r
     ≡⟨ cong! (+-comm m n) ⟩
      (n + m) % o % q ^ r
     ≡⟨ %-congʳ eq ⟨
      (n + m) % o % p
    ∎
