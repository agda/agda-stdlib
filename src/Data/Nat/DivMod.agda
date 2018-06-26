------------------------------------------------------------------------
-- The Agda standard library
--
-- Integer division
------------------------------------------------------------------------

module Data.Nat.DivMod where

open import Agda.Builtin.Nat using (div-helper; mod-helper)

open import Data.Fin using (Fin; toℕ; fromℕ≤″; fromℕ≤)
open import Data.Fin.Properties using (toℕ-fromℕ≤″)
open import Data.Nat as Nat
open import Data.Nat.DivMod.Core
open import Data.Nat.Properties using (≤⇒≤″)
open import Relation.Nullary.Decidable using (False)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.PropositionalEquality.TrustMe as TrustMe
  using (erase)

open ≡-Reasoning

------------------------------------------------------------------------
-- Basic operations

infixl 7 _div_ _%_

-- Integer division

_div_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
(a div 0) {}
(a div suc n) = div-helper 0 n a n

-- Integer remainder (mod)

_%_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
(a % 0) {}
(a % suc n) = mod-helper 0 n a n

------------------------------------------------------------------------
-- Proofs

a%1≡0 : ∀ a → a % 1 ≡ 0
a%1≡0 = a[modₕ]1≡0

a%n<n : ∀ a n → a % (suc n) < (suc n)
a%n<n a n = s≤s (mod-lemma 0 a n)

a≡a%n+[a/n]*n : ∀ a n → a ≡ a % suc n + (a div (suc n)) * suc n
a≡a%n+[a/n]*n a n = division-lemma 0 0 a n

[n+k]%n≡k%n : ∀ k n → (suc n + k) % suc n ≡ k % suc n
[n+k]%n≡k%n k n = {!!}

[k*n]%n≡0 : ∀ k n → k * (suc n) % (suc n) ≡ 0
[k*n]%n≡0 zero    n = refl
[k*n]%n≡0 (suc k) n = trans ([n+k]%n≡k%n (k * suc n) n) ([k*n]%n≡0 k n)

------------------------------------------------------------------------
-- Certified operations (i.e. operations with proofs)

-- A specification of integer division.

record DivMod (dividend divisor : ℕ) : Set where
  constructor result
  field
    quotient  : ℕ
    remainder : Fin divisor
    property  : dividend ≡ toℕ remainder + quotient * divisor

infixl 7 _mod_ _divMod_

-- Certified modulus

_mod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → Fin divisor
(a mod 0) {}
(a mod suc n) = fromℕ≤″ (a % suc n) (Nat.erase (≤⇒≤″ (a%n<n a n)))

-- Returns modulus and division result with correctness proof

_divMod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
           DivMod dividend divisor
(a divMod 0) {}
(a divMod suc n) = result (a div suc n) (a mod suc n)
  (TrustMe.erase (begin
    a                                                ≡⟨ a≡a%n+[a/n]*n a n ⟩
    (a % suc n)             + (a div suc n) * suc n  ≡⟨ cong₂ _+_ (sym (toℕ-fromℕ≤″ lemma′)) refl ⟩
    toℕ (fromℕ≤″ _ lemma′) + (a div suc n) * suc n  ∎))
  where
  lemma′ = Nat.erase (≤⇒≤″ (a%n<n a n))
