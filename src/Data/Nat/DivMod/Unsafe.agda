------------------------------------------------------------------------
-- The Agda standard library
--
-- More efficient (and unsafe) mod and divMod operations
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}

module Data.Nat.DivMod.Unsafe where

open import Data.Nat using (ℕ; _+_; _*_; _≟_; zero; suc)
open import Data.Nat.DivMod hiding (_mod_; _divMod_)
open import Data.Nat.Properties using (≤⇒≤″)
import Data.Nat.Unsafe as NatUnsafe
open import Data.Fin using (Fin; toℕ; fromℕ≤″)
open import Data.Fin.Properties using (toℕ-fromℕ≤″)
open import Function using (_$_)
open import Relation.Nullary.Decidable using (False)
open import Relation.Binary.PropositionalEquality
  using (refl; sym; cong; module ≡-Reasoning)
import Relation.Binary.PropositionalEquality.TrustMe as TrustMe
  using (erase)

open ≡-Reasoning

infixl 7 _mod_ _divMod_

------------------------------------------------------------------------
-- Certified modulus

_mod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → Fin divisor
(a mod 0) {}
(a mod suc n) = fromℕ≤″ (a % suc n) (NatUnsafe.erase (≤⇒≤″ (a%n<n a n)))

------------------------------------------------------------------------
-- Returns modulus and division result with correctness proof

_divMod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
           DivMod dividend divisor
(a divMod 0) {}
(a divMod suc n) = result (a div suc n) (a mod suc n) $ TrustMe.erase $ begin
  a                                 ≡⟨ a≡a%n+[a/n]*n a n ⟩
  a % suc n              + [a/n]*n  ≡⟨ cong (_+ [a/n]*n) (sym (toℕ-fromℕ≤″ lemma′)) ⟩
  toℕ (fromℕ≤″ _ lemma′) + [a/n]*n  ∎
  where
  lemma′ = NatUnsafe.erase (≤⇒≤″ (a%n<n a n))
  [a/n]*n = a div suc n * suc n
