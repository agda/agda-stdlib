------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural number division
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.DivMod where

open import Agda.Builtin.Nat using (div-helper; mod-helper)

open import Data.Fin.Base using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat.Base as Nat
open import Data.Nat.DivMod.Core
open import Data.Nat.Divisibility.Core
open import Data.Nat.Properties
open import Data.Nat.Tactic.RingSolver
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (False)

open ≤-Reasoning

------------------------------------------------------------------------
-- Definitions

-- The division and modulus operations are only defined when the divisor
-- is non-zero. The proof of this is defined as an irrelevant
-- implict argument of type `False (divisor ≟ 0)`. This allows this
-- proof to be automatically inferred when the divisor is of the form
-- `suc n`, and hence minimises the number of these proofs that
-- need be passed around. You can therefore write `m / suc n` without
-- issue.

infixl 7 _/_ _%_

-- Natural division

_/_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
m / (suc n) = div-helper 0 n m n

-- Natural remainder/modulus

_%_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
m % (suc n) = mod-helper 0 n m n

------------------------------------------------------------------------
-- Relationship between _%_ and _div_

m≡m%n+[m/n]*n : ∀ m n → m ≡ m % suc n + (m / suc n) * suc n
m≡m%n+[m/n]*n m n = div-mod-lemma 0 0 m n

m%n≡m∸m/n*n : ∀ m n → m % suc n ≡ m ∸ (m / suc n) * suc n
m%n≡m∸m/n*n m n-1 = begin-equality
  m % n                  ≡˘⟨ m+n∸n≡m (m % n) m/n*n ⟩
  m % n + m/n*n ∸ m/n*n  ≡˘⟨ cong (_∸ m/n*n) (m≡m%n+[m/n]*n m n-1) ⟩
  m ∸ m/n*n              ∎
  where n = suc n-1; m/n*n = (m / n) * n

------------------------------------------------------------------------
-- Properties of _%_

n%1≡0 : ∀ n → n % 1 ≡ 0
n%1≡0 = a[modₕ]1≡0

n%n≡0 : ∀ n → suc n % suc n ≡ 0
n%n≡0 n = n[modₕ]n≡0 0 n

m%n%n≡m%n : ∀ m n → m % suc n % suc n ≡ m % suc n
m%n%n≡m%n m n = modₕ-idem 0 m n

[m+n]%n≡m%n : ∀ m n → (m + suc n) % suc n ≡ m % suc n
[m+n]%n≡m%n m n = a+n[modₕ]n≡a[modₕ]n 0 m n

[m+kn]%n≡m%n : ∀ m k n → (m + k * (suc n)) % suc n ≡ m % suc n
[m+kn]%n≡m%n m zero    n-1 = cong (_% suc n-1) (+-identityʳ m)
[m+kn]%n≡m%n m (suc k) n-1 = begin-equality
  (m + (n + k * n)) % n ≡⟨ cong (_% n) (sym (+-assoc m n (k * n))) ⟩
  (m + n + k * n)   % n ≡⟨ [m+kn]%n≡m%n (m + n) k n-1 ⟩
  (m + n)           % n ≡⟨ [m+n]%n≡m%n m n-1 ⟩
  m                 % n ∎
  where n = suc n-1

m*n%n≡0 : ∀ m n → (m * suc n) % suc n ≡ 0
m*n%n≡0 = [m+kn]%n≡m%n 0

m%n<n : ∀ m n → m % suc n < suc n
m%n<n m n = s≤s (a[modₕ]n<n 0 m n)

m%n≤m : ∀ m n → m % suc n ≤ m
m%n≤m m n = a[modₕ]n≤a 0 m n

m≤n⇒m%n≡m : ∀ {m n} → m ≤ n → m % suc n ≡ m
m≤n⇒m%n≡m {m} {n} m≤n with ≤⇒≤″ m≤n
... | less-than-or-equal {k} refl = a≤n⇒a[modₕ]n≡a 0 (m + k) m k

%-pred-≡0 : ∀ {m n} {≢0} → (suc m % n) {≢0} ≡ 0 → (m % n) {≢0} ≡ n ∸ 1
%-pred-≡0 {m} {suc n-1} eq = a+1[modₕ]n≡0⇒a[modₕ]n≡n-1 0 n-1 m eq

m<[1+n%d]⇒m≤[n%d] : ∀ {m} n d {≢0} → m < (suc n % d) {≢0} → m ≤ (n % d) {≢0}
m<[1+n%d]⇒m≤[n%d] {m} n (suc d-1) = k<1+a[modₕ]n⇒k≤a[modₕ]n 0 m n d-1

[1+m%d]≤1+n⇒[m%d]≤n : ∀ m n d {≢0} → 0 < (suc m % d) {≢0} → (suc m % d) {≢0} ≤ suc n → (m % d) {≢0} ≤ n
[1+m%d]≤1+n⇒[m%d]≤n m n (suc d-1) leq = 1+a[modₕ]n≤1+k⇒a[modₕ]n≤k 0 n m d-1 leq

%-distribˡ-+ : ∀ m n d {≢0} → ((m + n) % d) {≢0} ≡ (((m % d) {≢0} + (n % d) {≢0}) % d) {≢0}
%-distribˡ-+ m n d@(suc d-1) = begin-equality
  (m + n)                         % d ≡⟨ cong (λ v → (v + n) % d) (m≡m%n+[m/n]*n m d-1) ⟩
  (m % d +  m / d * d + n)        % d ≡⟨ cong (_% d) (+-assoc (m % d) _ n) ⟩
  (m % d + (m / d * d + n))       % d ≡⟨ cong (λ v → (m % d + v) % d) (+-comm _ n) ⟩
  (m % d + (n + m / d * d))       % d ≡⟨ cong (_% d) (sym (+-assoc (m % d) n _)) ⟩
  (m % d +  n + m / d * d)        % d ≡⟨ [m+kn]%n≡m%n (m % d + n) (m / d) d-1 ⟩
  (m % d +  n)                    % d ≡⟨ cong (λ v → (m % d + v) % d) (m≡m%n+[m/n]*n n d-1) ⟩
  (m % d + (n % d + (n / d) * d)) % d ≡⟨ sym (cong (_% d) (+-assoc (m % d) (n % d) _)) ⟩
  (m % d +  n % d + (n / d) * d)  % d ≡⟨ [m+kn]%n≡m%n (m % d + n % d) (n / d) d-1 ⟩
  (m % d +  n % d)                % d ∎

%-distribˡ-* : ∀ m n d {≢0} → ((m * n) % d) {≢0} ≡ (((m % d) {≢0} * (n % d) {≢0}) % d) {≢0}
%-distribˡ-* m n d@(suc d-1) = begin-equality
  (m * n)                                             % d ≡⟨ cong (λ h → (h * n) % d) (m≡m%n+[m/n]*n m d-1) ⟩
  ((m′ + k * d) * n)                                  % d ≡⟨ cong (λ h → ((m′ + k * d) * h) % d) (m≡m%n+[m/n]*n n d-1) ⟩
  ((m′ + k * d) * (n′ + j * d))                       % d ≡⟨ cong (_% d) (lemma m′ n′ k j d) ⟩
  (m′ * n′ + (m′ * j + (n′ + j * d) * k) * d)         % d ≡⟨ [m+kn]%n≡m%n (m′ * n′) (m′ * j + (n′ + j * d) * k) d-1 ⟩
  (m′ * n′)                                           % d ≡⟨⟩
  ((m % d) * (n % d)) % d ∎
  where
  m′ = m % d
  n′ = n % d
  k = m / d
  j = n / d
  lemma : ∀ m′ n′ k j d → (m′ + k * d) * (n′ + j * d) ≡ m′ * n′ + (m′ * j + (n′ + j * d) * k) * d
  lemma = solve-∀

%-remove-+ˡ : ∀ {m} n {d} {≢0} → d ∣ m → ((m + n) % d) {≢0} ≡ (n % d) {≢0}
%-remove-+ˡ {m} n {d@(suc d-1)} (divides p refl) = begin-equality
  (p * d + n) % d ≡⟨ cong (_% d) (+-comm (p * d) n) ⟩
  (n + p * d) % d ≡⟨ [m+kn]%n≡m%n n p d-1 ⟩
  n           % d ∎

%-remove-+ʳ : ∀ m {n d} {≢0} → d ∣ n → ((m + n) % d) {≢0} ≡ (m % d) {≢0}
%-remove-+ʳ m {n} {suc _} eq rewrite +-comm m n = %-remove-+ˡ {n} m eq

------------------------------------------------------------------------
-- Properties of _/_

/-congˡ : ∀ {m n o : ℕ} {o≢0} → m ≡ n → (m / o) {o≢0} ≡ (n / o) {o≢0}
/-congˡ refl = refl

/-congʳ : ∀ {m n o : ℕ} {n≢0 o≢0} → n ≡ o →
         (m / n) {n≢0} ≡ (m / o) {o≢0}
/-congʳ {_} {suc _} {suc _} refl = refl

0/n≡0 : ∀ n {≢0} → (0 / n) {≢0} ≡ 0
0/n≡0 (suc n-1) = refl

n/1≡n : ∀ n → n / 1 ≡ n
n/1≡n n = a[divₕ]1≡a 0 n

n/n≡1 : ∀ n {≢0} → (n / n) {≢0} ≡ 1
n/n≡1 (suc n-1) = n[divₕ]n≡1 n-1 n-1

m*n/n≡m : ∀ m n {≢0} → (m * n / n) {≢0} ≡ m
m*n/n≡m m (suc n-1) = a*n[divₕ]n≡a 0 m n-1

m/n*n≡m : ∀ {m n} {≢0} → n ∣ m → (m / n) {≢0} * n ≡ m
m/n*n≡m {_} {n@(suc n-1)} (divides q refl) = cong (_* n) (m*n/n≡m q n)

m*[n/m]≡n : ∀ {m n} {≢0} → m ∣ n → m * (n / m) {≢0} ≡ n
m*[n/m]≡n {m} m∣n = trans (*-comm m (_ / m)) (m/n*n≡m m∣n)

m/n*n≤m : ∀ m n {≢0} → (m / n) {≢0} * n ≤ m
m/n*n≤m m n@(suc n-1) = begin
  (m / n) * n          ≤⟨ m≤m+n ((m / n) * n) (m % n) ⟩
  (m / n) * n + m % n  ≡⟨ +-comm _ (m % n) ⟩
  m % n + (m / n) * n  ≡⟨ sym (m≡m%n+[m/n]*n m n-1) ⟩
  m                    ∎

m/n<m : ∀ m n {≢0} → m ≥ 1 → n ≥ 2 → (m / n) {≢0} < m
m/n<m m n@(suc n-1) m≥1 n≥2 = *-cancelʳ-< {n} (m / n) m (begin-strict
  (m / n) * n ≤⟨ m/n*n≤m m n ⟩
  m           <⟨ m<m*n m≥1 n≥2 ⟩
  m * n       ∎)

/-mono-≤ : ∀ {m n o p} {o≢0 p≢0} → m ≤ n → o ≥ p → (m / o) {o≢0} ≤ (n / p) {p≢0}
/-mono-≤ m≤n (s≤s o≥p) = divₕ-mono-≤ 0 m≤n o≥p

/-monoˡ-≤ : ∀ {m n o} {o≢0} → m ≤ n → (m / o) {o≢0} ≤ (n / o) {o≢0}
/-monoˡ-≤ {o≢0 = o≢0} m≤n = /-mono-≤ {o≢0 = o≢0} {o≢0} m≤n ≤-refl

/-monoʳ-≤ : ∀ m {n o} {n≢0 o≢0} → n ≥ o → (m / n) {n≢0} ≤ (m / o) {o≢0}
/-monoʳ-≤ _ {n≢0 = n≢0} {o≢0} n≥o = /-mono-≤ {o≢0 = n≢0} {o≢0} ≤-refl n≥o

m≥n⇒m/n>0 : ∀ {m n n≢0} → m ≥ n → (m / n) {n≢0} > 0
m≥n⇒m/n>0 {m@(suc m-1)} {n@(suc n-1)} m≥n = begin
  1     ≡⟨ sym (n/n≡1 m) ⟩
  m / m ≤⟨ /-monoʳ-≤ m m≥n ⟩
  m / n ∎

+-distrib-/ : ∀ m n {d} {≢0} → (m % d) {≢0} + (n % d) {≢0} < d →
              ((m + n) / d) {≢0} ≡ (m / d) {≢0} + (n / d) {≢0}
+-distrib-/ m n {suc d-1} leq = +-distrib-divₕ 0 0 m n d-1 leq

+-distrib-/-∣ˡ : ∀ {m} n {d} {≢0} → d ∣ m →
                 ((m + n) / d) {≢0} ≡ (m / d) {≢0} + (n / d) {≢0}
+-distrib-/-∣ˡ {m} n {d@(suc d-1)} (divides p refl) = +-distrib-/ m n (begin-strict
  p * d % d + n % d ≡⟨ cong (_+ n % d) (m*n%n≡0 p d-1) ⟩
  n % d             <⟨ m%n<n n d-1 ⟩
  d                 ∎)

+-distrib-/-∣ʳ : ∀ {m} n {d} {≢0} → d ∣ n →
                 ((m + n) / d) {≢0} ≡ (m / d) {≢0} + (n / d) {≢0}
+-distrib-/-∣ʳ {m} n {d@(suc d-1)} (divides p refl) = +-distrib-/ m n (begin-strict
  m % d + p * d % d ≡⟨ cong (m % d +_) (m*n%n≡0 p d-1) ⟩
  m % d + 0         ≡⟨ +-identityʳ _ ⟩
  m % d             <⟨ m%n<n m d-1 ⟩
  d                 ∎)

*-/-assoc : ∀ m {n d} {≢0} → d ∣ n → (m * n / d) {≢0} ≡ m * ((n / d) {≢0})
*-/-assoc zero    {_} {d@(suc _)} d∣n = 0/n≡0 (suc d)
*-/-assoc (suc m) {n} {d@(suc _)} d∣n = begin-equality
  (n + m * n) / d     ≡⟨ +-distrib-/-∣ˡ _ d∣n ⟩
  n / d + (m * n) / d ≡⟨ cong (n / d +_) (*-/-assoc m d∣n) ⟩
  n / d + m * (n / d) ∎

------------------------------------------------------------------------
--  A specification of integer division.

record DivMod (dividend divisor : ℕ) : Set where
  constructor result
  field
    quotient  : ℕ
    remainder : Fin divisor
    property  : dividend ≡ toℕ remainder + quotient * divisor

infixl 7 _div_ _mod_ _divMod_

_div_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
_div_ = _/_

_mod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → Fin divisor
m mod (suc n) = fromℕ< (m%n<n m n)

_divMod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
           DivMod dividend divisor
m divMod n@(suc n-1) = result (m / n) (m mod n) (begin-equality
  m                                     ≡⟨ m≡m%n+[m/n]*n m n-1 ⟩
  m % n                      + [m/n]*n  ≡⟨ cong (_+ [m/n]*n) (sym (toℕ-fromℕ< (m%n<n m n-1))) ⟩
  toℕ (fromℕ< (m%n<n m n-1)) + [m/n]*n  ∎)
  where [m/n]*n = m / n * n

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

a≡a%n+[a/n]*n = m≡m%n+[m/n]*n
{-# WARNING_ON_USAGE a≡a%n+[a/n]*n
"Warning: a≡a%n+[a/n]*n was deprecated in v1.1.
Please use m≡m%n+[m/n]*n instead."
#-}
a%1≡0   = n%1≡0
{-# WARNING_ON_USAGE a%1≡0
"Warning: a%1≡0 was deprecated in v1.1.
Please use n%1≡0 instead."
#-}
a%n%n≡a%n = m%n%n≡m%n
{-# WARNING_ON_USAGE a%n%n≡a%n
"Warning: a%n%n≡a%n was deprecated in v1.1.
Please use m%n%n≡m%n instead."
#-}
[a+n]%n≡a%n = [m+n]%n≡m%n
{-# WARNING_ON_USAGE [a+n]%n≡a%n
"Warning: [a+n]%n≡a%n was deprecated in v1.1.
Please use [m+n]%n≡m%n instead."
#-}
[a+kn]%n≡a%n = [m+kn]%n≡m%n
{-# WARNING_ON_USAGE [a+kn]%n≡a%n
"Warning: [a+kn]%n≡a%n was deprecated in v1.1.
Please use [m+kn]%n≡m%n instead."
#-}
kn%n≡0 = m*n%n≡0
{-# WARNING_ON_USAGE kn%n≡0
"Warning: kn%n≡0 was deprecated in v1.1.
Please use m*n%n≡0 instead."
#-}
a%n<n = m%n<n
{-# WARNING_ON_USAGE a%n<n
"Warning: a%n<n was deprecated in v1.1.
Please use m%n<n instead."
#-}
