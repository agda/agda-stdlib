------------------------------------------------------------------------
-- The Agda standard library
--
-- Least Common Multiple for integers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Integer.LCM where

open import Data.Integer.Base
open import Data.Integer.Divisibility using (_∣_)
open import Data.Integer.GCD using (gcd)
import Data.Nat.LCM as ℕ
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong)

------------------------------------------------------------------------
-- Definition
------------------------------------------------------------------------

lcm : ℤ → ℤ → ℤ
lcm i j = + ℕ.lcm ∣ i ∣ ∣ j ∣

------------------------------------------------------------------------
-- Properties
------------------------------------------------------------------------

i∣lcm[i,j] : ∀ i j → i ∣ lcm i j
i∣lcm[i,j] i j = ℕ.m∣lcm[m,n] ∣ i ∣ ∣ j ∣

j∣lcm[i,j] : ∀ i j → j ∣ lcm i j
j∣lcm[i,j] i j = ℕ.n∣lcm[m,n] ∣ i ∣ ∣ j ∣

lcm-least : ∀ {i j c} → i ∣ c → j ∣ c → lcm i j ∣ c
lcm-least c∣i c∣j = ℕ.lcm-least c∣i c∣j

lcm[0,i]≡0 : ∀ i → lcm 0ℤ i ≡ 0ℤ
lcm[0,i]≡0 i = cong (+_) (ℕ.lcm[0,n]≡0 ∣ i ∣)

lcm[i,0]≡0 : ∀ i → lcm i 0ℤ ≡ 0ℤ
lcm[i,0]≡0 i = cong (+_) (ℕ.lcm[n,0]≡0 ∣ i ∣)

lcm-comm : ∀ i j → lcm i j ≡ lcm j i
lcm-comm i j = cong (+_) (ℕ.lcm-comm ∣ i ∣ ∣ j ∣)
