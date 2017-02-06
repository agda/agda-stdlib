------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe functions on digits and digit expansions
------------------------------------------------------------------------

module Unsafe.Data.Digit where

open import Data.Digit public

open import Data.Nat
open import Data.Nat.Properties
open SemiringSolver
open import Data.Fin as Fin using (Fin; zero; suc; toℕ)
open import Relation.Nullary.Decidable
open import Data.Char using (Char)
open import Data.List.Base
open import Data.Product
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Induction.Nat
open import Unsafe.Data.Nat.DivMod
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Function

------------------------------------------------------------------------
-- A boring lemma

private

  lem : ∀ x k r → 2 + x ≤′ r + (1 + x) * (2 + k)
  lem x k r = ≤⇒≤′ $ begin
    2 + x
      ≤⟨ m≤m+n _ _ ⟩
    2 + x + (x + (1 + x) * k + r)
      ≡⟨ solve 3 (λ x r k → con 2 :+ x :+ (x :+ (con 1 :+ x) :* k :+ r)
                              :=
                            r :+ (con 1 :+ x) :* (con 2 :+ k))
                 refl x r k ⟩
    r + (1 + x) * (2 + k)
      ∎

-- toDigits b n yields the digits of n, in base b, starting with the
-- _least_ significant digit.
--
-- Note that the list of digits is always non-empty.

toDigits : (base : ℕ) {base≥2 : True (2 ≤? base)} (n : ℕ) →
           ∃ λ (ds : List (Fin base)) → fromDigits ds ≡ n
toDigits zero       {base≥2 = ()} _
toDigits (suc zero) {base≥2 = ()} _
toDigits (suc (suc k)) n = <-rec Pred helper n
  where
  base = suc (suc k)
  Pred = λ n → ∃ λ ds → fromDigits ds ≡ n

  cons : ∀ {m} (r : Fin base) → Pred m → Pred (toℕ r + m * base)
  cons r (ds , eq) = (r ∷ ds , P.cong (λ i → toℕ r + i * base) eq)

  helper : ∀ n → <-Rec Pred n → Pred n
  helper n                       rec with n divMod base
  helper .(toℕ r + 0     * base) rec | result zero    r refl = ([ r ] , refl)
  helper .(toℕ r + suc x * base) rec | result (suc x) r refl =
    cons r (rec (suc x) (lem (pred (suc x)) k (toℕ r)))
