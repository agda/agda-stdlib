------------------------------------------------------------------------
-- The Agda standard library
--
-- Exponentiation defined over a semiring as repeated multiplication
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_)
import Data.Nat.Properties as ℕ

module Algebra.Properties.Semiring.Exp
  {a ℓ} (S : Semiring a ℓ) where

open Semiring S
open import Relation.Binary.Reasoning.Setoid setoid
import Algebra.Properties.Monoid.Mult *-monoid as Mult

------------------------------------------------------------------------
-- Definition

open import Algebra.Definitions.RawSemiring rawSemiring public
  using (_^_)

------------------------------------------------------------------------
-- Properties

^-congˡ : ∀ n → (_^ n) Preserves _≈_ ⟶ _≈_
^-congˡ = Mult.×-congʳ

^-cong : _^_ Preserves₂ _≈_ ⟶ _≡_ ⟶ _≈_
^-cong x≈y u≡v = Mult.×-cong u≡v x≈y

^-congʳ : ∀ x → (x ^_) Preserves _≡_ ⟶ _≈_
^-congʳ x = Mult.×-congˡ

-- xᵐ⁺ⁿ ≈ xᵐxⁿ
^-homo-* : ∀ x m n → x ^ (m ℕ.+ n) ≈ (x ^ m) * (x ^ n)
^-homo-* = Mult.×-homo-+

-- (xᵐ)ⁿ≈xᵐ*ⁿ
^-assocʳ : ∀ x m n → (x ^ m) ^ n ≈ x ^ (m ℕ.* n)
^-assocʳ x m n rewrite ℕ.*-comm m n = Mult.×-assocˡ x n m

------------------------------------------------------------------------
-- A lemma using commutativity, needed for the Binomial Theorem

y*x^m*y^n≈x^m*y^[n+1] : ∀ {x} {y} (x*y≈y*x : x * y ≈ y * x) →
                        ∀ m n → y * (x ^ m * y ^ n) ≈ x ^ m * y ^ suc n
y*x^m*y^n≈x^m*y^[n+1] {x} {y} x*y≈y*x = helper
  where
    helper : ∀ m n → y * (x ^ m * y ^ n) ≈ x ^ m * y ^ suc n
    helper zero    n = begin
      y * (x ^ ℕ.zero * y ^ n)  ≡⟨⟩
      y * (1# * y ^ n)          ≈⟨ *-congˡ (*-identityˡ (y ^ n)) ⟩
      y * (y ^ n)               ≡⟨⟩
      y ^ (suc n)               ≈˘⟨ *-identityˡ (y ^ suc n) ⟩
      1# * y ^ (suc n)          ≡⟨⟩
      x ^ ℕ.zero * y ^ (suc n)  ∎
    helper (suc m) n = begin
      y * (x ^ suc m * y ^ n)    ≡⟨⟩
      y * ((x * x ^ m) * y ^ n)  ≈⟨ *-congˡ (*-assoc x (x ^ m) (y ^ n)) ⟩
      y * (x * (x ^ m * y ^ n))  ≈˘⟨ *-assoc y x (x ^ m * y ^ n) ⟩
      y * x * (x ^ m * y ^ n)    ≈˘⟨ *-congʳ x*y≈y*x ⟩
      x * y * (x ^ m * y ^ n)    ≈⟨ *-assoc x y _ ⟩
      x * (y * (x ^ m * y ^ n))  ≈⟨ *-congˡ (helper m n) ⟩
      x * (x ^ m * y ^ suc n)    ≈˘⟨ *-assoc x (x ^ m) (y ^ suc n) ⟩
      (x * x ^ m) * y ^ suc n    ≡⟨⟩
      x ^ suc m * y ^ suc n      ∎
