------------------------------------------------------------------------
-- The Agda standard library
--
-- More efficient mod and divMod operations (require the K axiom)
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Nat.DivMod.WithK where

open import Data.Nat using (ℕ; _+_; _*_; _≟_; zero; suc)
open import Data.Nat.DivMod hiding (_mod_; _divMod_)
open import Data.Nat.Properties using (≤⇒≤″)
open import Data.Nat.WithK
open import Data.Fin using (Fin; toℕ; fromℕ≤″)
open import Data.Fin.Properties using (toℕ-fromℕ≤″)
open import Function using (_$_)
open import Relation.Nullary.Decidable using (False)
open import Relation.Binary.PropositionalEquality
  using (refl; sym; cong; module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality.WithK

open ≡-Reasoning

infixl 7 _mod_ _divMod_

------------------------------------------------------------------------
-- Certified modulus

_mod_ : (dividend divisor : ℕ) .{≢0 : False (divisor ≟ 0)} → Fin divisor
a mod (suc n) = fromℕ≤″ (a % suc n) (≤″-erase (≤⇒≤″ (a%n<n a n)))

------------------------------------------------------------------------
-- Returns modulus and division result with correctness proof

_divMod_ : (dividend divisor : ℕ) .{≢0 : False (divisor ≟ 0)} →
           DivMod dividend divisor
a divMod (suc n) = result (a / suc n) (a mod suc n) $ ≡-erase $ begin
  a                                 ≡⟨ a≡a%n+[a/n]*n a n ⟩
  a % suc n              + [a/n]*n  ≡⟨ cong (_+ [a/n]*n) (sym (toℕ-fromℕ≤″ lemma′)) ⟩
  toℕ (fromℕ≤″ _ lemma′) + [a/n]*n  ∎
  where
  lemma′ = ≤″-erase (≤⇒≤″ (a%n<n a n))
  [a/n]*n = a / suc n * suc n
