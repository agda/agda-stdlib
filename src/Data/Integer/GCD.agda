------------------------------------------------------------------------
-- The Agda standard library
--
-- Greatest Common Divisor for integers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Integer.GCD where

open import Data.Integer.Base
open import Data.Integer.Divisibility
open import Data.Integer.Properties
open import Data.Nat.Base
import Data.Nat.GCD as ℕ
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Definition
------------------------------------------------------------------------

gcd : ℤ → ℤ → ℤ
gcd i j = + ℕ.gcd ∣ i ∣ ∣ j ∣

------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------

gcd[i,j]∣i : ∀ i j → gcd i j ∣ i
gcd[i,j]∣i i j = ℕ.gcd[m,n]∣m ∣ i ∣ ∣ j ∣

gcd[i,j]∣j : ∀ i j → gcd i j ∣ j
gcd[i,j]∣j i j = ℕ.gcd[m,n]∣n ∣ i ∣ ∣ j ∣

gcd-greatest : ∀ {i j c} → c ∣ i → c ∣ j → c ∣ gcd i j
gcd-greatest c∣i c∣j = ℕ.gcd-greatest c∣i c∣j

gcd[0,0]≡0 : gcd 0ℤ 0ℤ ≡ 0ℤ
gcd[0,0]≡0 = cong (+_) ℕ.gcd[0,0]≡0

gcd[i,j]≡0⇒i≡0 : ∀ i j → gcd i j ≡ 0ℤ → i ≡ 0ℤ
gcd[i,j]≡0⇒i≡0 i j eq = ∣n∣≡0⇒n≡0 (ℕ.gcd[m,n]≡0⇒m≡0 (+-injective eq))

gcd[i,j]≡0⇒j≡0 : ∀ {i j} → gcd i j ≡ 0ℤ → j ≡ 0ℤ
gcd[i,j]≡0⇒j≡0 {i} eq = ∣n∣≡0⇒n≡0 (ℕ.gcd[m,n]≡0⇒n≡0 ∣ i ∣ (+-injective eq))

gcd-comm : ∀ i j → gcd i j ≡ gcd j i
gcd-comm i j = cong (+_) (ℕ.gcd-comm ∣ i ∣ ∣ j ∣)
