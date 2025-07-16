------------------------------------------------------------------------
-- The Agda standard library
--
-- Coprimality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Integer.Coprimality where

open import Data.Integer.Base using (ℤ; _*_; ∣_∣)
open import Data.Integer.Divisibility using (_∣_)
open import Data.Integer.Properties using (abs-*)
import Data.Nat.Coprimality as ℕ
  using (Coprime; sym; coprime?; coprime-divisor)
import Data.Nat.Divisibility as ℕ using (_∣_)
open import Function.Base using (_on_)
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Decidable; Symmetric)
open import Relation.Binary.PropositionalEquality.Core using (subst)

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
  ℕ.coprime-divisor c (subst (∣ i ∣ ℕ.∣_ ) (abs-* j k) eq)
