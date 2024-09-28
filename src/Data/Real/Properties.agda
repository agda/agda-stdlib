------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of real numbers
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible --guardedness #-}

module Data.Real.Properties where

open import Data.Real.Base

open import Algebra.Definitions _≈_
open import Codata.Guarded.Stream
open import Codata.Guarded.Stream.Properties
import Codata.Guarded.Stream.Relation.Binary.Pointwise as PW
open import Data.Product.Base
import Data.Integer.Base as ℤ
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
import Data.Rational.Base as ℚ
import Data.Rational.Properties as ℚ
open import Data.Rational.Solver
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

+-cong : Congruent₂ _+_
+-cong {x} {y} {u} {v} x≈y u≈v ε = proj₁ (x≈y (ℚ.½ ℚ.* ε)) ℕ.⊔ proj₁ (u≈v (ℚ.½ ℚ.* ε)) , λ {n} n≥N → begin-strict
  ℚ.∣ lookup (zipWith ℚ._+_ (sequence x) (sequence u)) n ℚ.- lookup (zipWith ℚ._+_ (sequence y) (sequence v)) n ∣
    ≡⟨ cong₂ (λ a b → ℚ.∣ a ℚ.- b ∣) (lookup-zipWith n ℚ._+_ (sequence x) (sequence u)) (lookup-zipWith n ℚ._+_ (sequence y) (sequence v)) ⟩
  ℚ.∣ (lookup (sequence x) n ℚ.+ lookup (sequence u) n) ℚ.- (lookup (sequence y) n ℚ.+ lookup (sequence v) n) ∣
    ≡⟨ cong ℚ.∣_∣ (lemma (lookup (sequence x) n) (lookup (sequence u) n) (lookup (sequence y) n) (lookup (sequence v) n)) ⟩
  ℚ.∣ (lookup (sequence x) n ℚ.- lookup (sequence y) n) ℚ.+ (lookup (sequence u) n ℚ.- lookup (sequence v) n) ∣
    ≤⟨ ℚ.∣p+q∣≤∣p∣+∣q∣ (lookup (sequence x) n ℚ.- lookup (sequence y) n) (lookup (sequence u) n ℚ.- lookup (sequence v) n) ⟩
  ℚ.∣ lookup (sequence x) n ℚ.- lookup (sequence y) n ∣ ℚ.+ ℚ.∣ lookup (sequence u) n ℚ.- lookup (sequence v) n ∣
    <⟨ ℚ.+-mono-<
      (proj₂ (x≈y (ℚ.½ ℚ.* ε)) (ℕ.≤-trans (ℕ.m≤m⊔n (proj₁ (x≈y (ℚ.½ ℚ.* ε))) (proj₁ (u≈v (ℚ.½ ℚ.* ε)))) n≥N))
      (proj₂ (u≈v (ℚ.½ ℚ.* ε)) (ℕ.≤-trans (ℕ.m≤n⊔m (proj₁ (x≈y (ℚ.½ ℚ.* ε))) (proj₁ (u≈v (ℚ.½ ℚ.* ε)))) n≥N))
    ⟩
  ℚ.½ ℚ.* ε ℚ.+ ℚ.½ ℚ.* ε
    ≡˘⟨ ℚ.*-distribʳ-+ ε ℚ.½ ℚ.½ ⟩
  ℚ.1ℚ ℚ.* ε
    ≡⟨ ℚ.*-identityˡ ε ⟩
  ε ∎
  where
    open ℚ.≤-Reasoning
    instance _ : ℚ.Positive (ℚ.½ ℚ.* ε)
    _ = ℚ.pos*pos⇒pos ℚ.½ ε

    lemma : ∀ a b c d → (a ℚ.+ b) ℚ.- (c ℚ.+ d) ≡ (a ℚ.- c) ℚ.+ (b ℚ.- d)
    lemma = solve 4 (λ a b c d → ((a :+ b) :- (c :+ d)) , ((a :- c) :+ (b :- d))) refl
      where open +-*-Solver

+-assoc : Associative _+_
+-assoc x y z ε = 0 , λ {n} _ → begin-strict
  ℚ.∣ lookup (zipWith ℚ._+_ (zipWith ℚ._+_ (sequence x) (sequence y)) (sequence z)) n ℚ.- lookup (zipWith ℚ._+_ (sequence x) (zipWith ℚ._+_ (sequence y) (sequence z))) n ∣
    ≡⟨ ℚ.d-definite (cong-lookup (PW.assoc ℚ.+-assoc (sequence x) (sequence y) (sequence z)) n) ⟩
  ℚ.0ℚ
    <⟨ ℚ.positive⁻¹ ε ⟩
  ε ∎
  where open ℚ.≤-Reasoning

+-comm : Commutative _+_
+-comm x y ε = 0 , λ {n} _ → begin-strict
  ℚ.∣ lookup (zipWith ℚ._+_ (sequence x) (sequence y)) n ℚ.- lookup (zipWith ℚ._+_ (sequence y) (sequence x)) n ∣
    ≡⟨ ℚ.d-definite (cong-lookup (PW.comm ℚ.+-comm (sequence x) (sequence y)) n) ⟩
  ℚ.0ℚ
    <⟨ ℚ.positive⁻¹ ε ⟩
  ε ∎
  where open ℚ.≤-Reasoning

+-identityˡ : LeftIdentity 0ℝ _+_
+-identityˡ x ε = 0 , λ {n} _ → begin-strict
  ℚ.∣ lookup (zipWith ℚ._+_ (repeat ℚ.0ℚ) (sequence x)) n ℚ.- lookup (sequence x) n ∣
    ≡⟨ ℚ.d-definite (cong-lookup (PW.identityˡ ℚ.+-identityˡ (sequence x)) n) ⟩
  ℚ.0ℚ
    <⟨ ℚ.positive⁻¹ ε ⟩
  ε ∎
  where open ℚ.≤-Reasoning

