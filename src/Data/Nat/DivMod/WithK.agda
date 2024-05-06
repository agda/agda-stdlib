------------------------------------------------------------------------
-- The Agda standard library
--
-- More efficient mod and divMod operations (require the K axiom)
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Nat.DivMod.WithK where

open import Data.Nat.Base using (ℕ; NonZero; _+_; _*_)
open import Data.Nat.DivMod hiding (_mod_; _divMod_)
open import Data.Nat.Properties using (≤⇒≤″)
open import Data.Nat.WithK using (≤″-erase)
open import Data.Fin.Base using (Fin; toℕ; fromℕ<″)
open import Data.Fin.Properties using (toℕ-fromℕ<″)
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.WithK using (≡-erase)

open ≡-Reasoning

infixl 7 _mod_ _divMod_

------------------------------------------------------------------------
-- Certified modulus

_mod_ : (dividend divisor : ℕ) → .{{ _ : NonZero divisor }} → Fin divisor
m mod n = fromℕ<″ (m % n) (≤″-erase (≤⇒≤″ (m%n<n m n)))

------------------------------------------------------------------------
-- Returns modulus and division result with correctness proof

_divMod_ : (dividend divisor : ℕ) → .{{ NonZero divisor }} →
           DivMod dividend divisor
m divMod n = result (m / n) (m mod n) $ ≡-erase $ begin
  m                                 ≡⟨ m≡m%n+[m/n]*n m n ⟩
  m % n                  + [m/n]*n  ≡⟨ cong (_+ [m/n]*n) (toℕ-fromℕ<″ lemma″) ⟨
  toℕ (fromℕ<″ _ lemma″) + [m/n]*n  ∎
  where [m/n]*n = m / n * n ; lemma″ = ≤″-erase (≤⇒≤″ (m%n<n m n))
