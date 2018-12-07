------------------------------------------------------------------------
-- The Agda standard library
--
-- Coprimality
------------------------------------------------------------------------

module Data.Integer.Coprimality where

open import Data.Integer
open import Data.Integer.Divisibility
open import Data.Integer.Properties
import Data.Nat.Coprimality as ℕ
import Data.Nat.Divisibility as ℕ
open import Function using (_on_)
open import Level using (0ℓ)
open import Relation.Binary using (Rel; Decidable; Symmetric)
open import Relation.Binary.PropositionalEquality using (subst)

------------------------------------------------------------------------
-- Definition

Coprime : Rel ℤ 0ℓ
Coprime = ℕ.Coprime on ∣_∣

------------------------------------------------------------------------
-- Properties of coprimality

sym : Symmetric Coprime
sym = ℕ.sym

coprime? : Decidable Coprime
coprime? x y = ℕ.coprime? ∣ x ∣ ∣ y ∣

coprime-divisor : ∀ i j k → Coprime i j → i ∣ j * k → i ∣ k
coprime-divisor i j k c eq =
  ℕ.coprime-divisor c (subst (∣ i ∣ ℕ.∣_ ) (abs-*-commute j k) eq)
