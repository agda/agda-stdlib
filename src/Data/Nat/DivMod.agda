------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural number division
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.DivMod where

open import Agda.Builtin.Nat using (div-helper; mod-helper)

open import Data.Fin using (Fin; toℕ; fromℕ≤)
open import Data.Fin.Properties using (toℕ-fromℕ≤)
open import Data.Nat as Nat
open import Data.Nat.DivMod.Core
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (False)

open ≤-Reasoning


------------------------------------------------------------------------
-- Basic operations

infixl 7 _div_ _%_

-- Integer division

_div_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
a div (suc n) = div-helper 0 n a n

-- Integer remainder (mod)

_%_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
a % (suc n) = mod-helper 0 n a n

------------------------------------------------------------------------
-- Properties

a≡a%n+[a/n]*n : ∀ a n → a ≡ a % suc n + (a div (suc n)) * suc n
a≡a%n+[a/n]*n a n = division-lemma 0 0 a n

a%1≡0 : ∀ a → a % 1 ≡ 0
a%1≡0 = a[modₕ]1≡0

a%n<n : ∀ a n → a % suc n < suc n
a%n<n a n = s≤s (a[modₕ]n<n 0 a n)

n%n≡0 : ∀ n → suc n % suc n ≡ 0
n%n≡0 n = n[modₕ]n≡0 0 n

a%n%n≡a%n : ∀ a n → a % suc n % suc n ≡ a % suc n
a%n%n≡a%n a n = modₕ-idem 0 a n

[a+n]%n≡a%n : ∀ a n → (a + suc n) % suc n ≡ a % suc n
[a+n]%n≡a%n a n = a+n[modₕ]n≡a[modₕ]n 0 a n

[a+kn]%n≡a%n : ∀ a k n → (a + k * (suc n)) % suc n ≡ a % suc n
[a+kn]%n≡a%n a zero    n-1 = cong (_% suc n-1) (+-identityʳ a)
[a+kn]%n≡a%n a (suc k) n-1 = begin-equality
  (a + (n + k * n)) % n ≡⟨ cong (_% n) (sym (+-assoc a n (k * n))) ⟩
  (a + n + k * n)   % n ≡⟨ [a+kn]%n≡a%n (a + n) k n-1 ⟩
  (a + n)           % n ≡⟨ [a+n]%n≡a%n a n-1 ⟩
  a                 % n ∎
  where n = suc n-1

kn%n≡0 : ∀ k n → k * (suc n) % suc n ≡ 0
kn%n≡0 = [a+kn]%n≡a%n 0

[a/n]*n≤a : ∀ a n → (a div (suc n)) * (suc n) ≤ a
[a/n]*n≤a a n-1 = begin
  (a div n) * n          ≤⟨ m≤m+n ((a div n) * n) (a % n) ⟩
  (a div n) * n + a % n  ≡⟨ +-comm _ (a % n) ⟩
  a % n + (a div n) * n  ≡⟨ sym (a≡a%n+[a/n]*n a n-1) ⟩
  a                      ∎
  where n = suc n-1

%-distribˡ-+ : ∀ a b n → (a + b) % suc n ≡ (a % suc n + b % suc n) % suc n
%-distribˡ-+ a b n-1 = begin-equality
  (a + b)                           % n ≡⟨ cong (λ v → (v + b) % n) (a≡a%n+[a/n]*n a n-1) ⟩
  (a % n +  a div n * n + b)        % n ≡⟨ cong (_% n) (+-assoc (a % n) _ b) ⟩
  (a % n + (a div n * n + b))       % n ≡⟨ cong (λ v → (a % n + v) % n) (+-comm _ b) ⟩
  (a % n + (b + a div n * n))       % n ≡⟨ cong (_% n) (sym (+-assoc (a % n) b _)) ⟩
  (a % n +  b + a div n * n)        % n ≡⟨ [a+kn]%n≡a%n (a % n + b) (a div n) n-1 ⟩
  (a % n +  b)                      % n ≡⟨ cong (λ v → (a % n + v) % n) (a≡a%n+[a/n]*n b n-1) ⟩
  (a % n + (b % n + (b div n) * n)) % n ≡⟨ sym (cong (_% n) (+-assoc (a % n) (b % n) _)) ⟩
  (a % n +  b % n + (b div n) * n)  % n ≡⟨ [a+kn]%n≡a%n (a % n + b % n) (b div n) n-1 ⟩
  (a % n +  b % n)                  % n ∎
  where n = suc n-1

------------------------------------------------------------------------
--  A specification of integer division.

record DivMod (dividend divisor : ℕ) : Set where
  constructor result
  field
    quotient  : ℕ
    remainder : Fin divisor
    property  : dividend ≡ toℕ remainder + quotient * divisor

_mod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → Fin divisor
(a mod 0) {}
(a mod suc n) = fromℕ≤ (a%n<n a n)

_divMod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
           DivMod dividend divisor
(a divMod 0) {}
(a divMod suc n) = result (a div suc n) (a mod suc n) (begin-equality
  a                                   ≡⟨ a≡a%n+[a/n]*n a n ⟩
  a % suc n                + [a/n]*n  ≡⟨ cong (_+ [a/n]*n) (sym (toℕ-fromℕ≤ (a%n<n a n))) ⟩
  toℕ (fromℕ≤ (a%n<n a n)) + [a/n]*n  ∎)
  where [a/n]*n = a div suc n * suc n
