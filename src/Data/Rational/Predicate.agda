------------------------------------------------------------------------
-- The Agda standard library
--
-- Simple predicates over ℕ
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Predicate where

open import Data.Rational.Base
open import Data.Integer as ℤ using (+0; -[1+_]; +[1+_]; _◃_; ∣_∣)
import Data.Integer.Predicate as ℤ
import Data.Integer.Properties as ℤ
open import Data.Nat using (zero; suc)
open import Data.Nat.Coprimality using (coprime?; ¬0-coprimeTo-2+)
open import Data.Integer.Properties
open import Level using (0ℓ)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym)
open import Relation.Unary using (Pred)

open ≤-Reasoning

------------------------------------------------------------------------
-- Definition

NonZero : Pred ℚ 0ℓ
NonZero p = ℤ.NonZero (↥ p)

Positive : Pred ℚ 0ℓ
Positive p = ℤ.Positive (↥ p)

Negative : Pred ℚ 0ℓ
Negative p = ℤ.Negative (↥ p)

NonPositive : Pred ℚ 0ℓ
NonPositive p = ℤ.NonPositive (↥ p)

NonNegative : Pred ℚ 0ℓ
NonNegative p = ℤ.NonNegative (↥ p)

------------------------------------------------------------------------
-- Constructors

nonZero : ∀ {p} → p ≢ 0ℚ → NonZero p
nonZero {mkℚ -[1+ _ ] _ _}       p≢0 = _
nonZero {mkℚ +[1+ _ ] _ _}       p≢0 = _
nonZero {mkℚ +0       zero    _} p≢0 = p≢0 refl
nonZero {mkℚ +0       (suc d) c} p≢0 = ¬0-coprimeTo-2+ (recompute (coprime? _ _) c)

positive : ∀ {p} → 0ℚ < p → Positive p
positive {p} (*<* 0<p) = fromWitness (begin-strict
  +0             ≡⟨⟩
  ↥ 0ℚ ℤ.* ↧ p   <⟨ 0<p ⟩
  ↥ p  ℤ.* ↧ 0ℚ  ≡⟨ ℤ.*-identityʳ (↥ p) ⟩
  ↥ p            ∎)

negative : ∀ {p} → p < 0ℚ → Negative p
negative {p} (*<* p<0) = fromWitness (begin-strict
  ↥ p            ≡⟨ sym (ℤ.*-identityʳ (↥ p)) ⟩
  ↥ p  ℤ.* ↧ 0ℚ  <⟨ p<0 ⟩
  ↥ 0ℚ ℤ.* ↧ p   ≡⟨⟩
  ↥ 0ℚ           ∎)

nonPositive : ∀ {p} → p ≤ 0ℚ → NonPositive p
nonPositive {p} (*≤* p≤0) = fromWitness (begin
  ↥ p            ≡⟨ sym (ℤ.*-identityʳ (↥ p)) ⟩
  ↥ p  ℤ.* ↧ 0ℚ  ≤⟨ p≤0 ⟩
  ↥ 0ℚ ℤ.* ↧ p   ≡⟨⟩
  ↥ 0ℚ           ∎)

nonNegative : ∀ {p} → 0ℚ ≤ p → NonNegative p
nonNegative {p} (*≤* 0≤p) = fromWitness (begin
  +0             ≡⟨⟩
  ↥ 0ℚ ℤ.* ↧ p   ≤⟨ 0≤p ⟩
  ↥ p  ℤ.* ↧ 0ℚ  ≡⟨ ℤ.*-identityʳ (↥ p) ⟩
  ↥ p            ∎)
