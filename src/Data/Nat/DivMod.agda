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
open import Data.Nat.Divisibility.Core
open import Data.Nat.Properties
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

_/_ : (dividend divisor : ℕ) .{≢0 : False (divisor ≟ 0)} → ℕ
m / (suc n) = div-helper 0 n m n

-- Natural remainder/modulus

_%_ : (dividend divisor : ℕ) .{≢0 : False (divisor ≟ 0)} → ℕ
m % (suc n) = mod-helper 0 n m n

------------------------------------------------------------------------
-- Relationship between _%_ and _div_

a≡a%n+[a/n]*n : ∀ a n → a ≡ a % suc n + (a / (suc n)) * suc n
a≡a%n+[a/n]*n a n = div-mod-lemma 0 0 a n

a%n=a∸a/n*n : ∀ a n → a % suc n ≡ a ∸ (a / suc n) * suc n
a%n=a∸a/n*n a n-1 = begin-equality
  a % n                  ≡˘⟨ m+n∸n≡m (a % n) a/n*n ⟩
  a % n + a/n*n ∸ a/n*n  ≡˘⟨ cong (_∸ a/n*n) (a≡a%n+[a/n]*n a n-1) ⟩
  a ∸ a/n*n              ∎
  where n = suc n-1; a/n*n = (a / n) * n

------------------------------------------------------------------------
-- Properties of _%_

a%1≡0 : ∀ a → a % 1 ≡ 0
a%1≡0 = a[modₕ]1≡0

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

kn%n≡0 : ∀ k n → (k * suc n) % suc n ≡ 0
kn%n≡0 = [a+kn]%n≡a%n 0

a%n<n : ∀ a n → a % suc n < suc n
a%n<n a n = s≤s (a[modₕ]n<n 0 a n)

a%n≤a : ∀ a n → a % suc n ≤ a
a%n≤a a n = a[modₕ]n≤a 0 a n

a≤n⇒a%n≡a : ∀ {a n} → a ≤ n → a % suc n ≡ a
a≤n⇒a%n≡a {a} {n} a≤n with ≤⇒≤″ a≤n
... | less-than-or-equal {k} refl = a≤n⇒a[modₕ]n≡a 0 (a + k) a k

a+1%n≡0⇒a%n≡n-1 : ∀ {a n} → suc a % suc n ≡ 0 → a % suc n ≡ n
a+1%n≡0⇒a%n≡n-1 {a} {n} eq = a+1[modₕ]n≡0⇒a[modₕ]n≡n-1 0 n a eq

m<1+a%n⇒m≤a%n : ∀ {m} a n → m < suc a % suc n → m ≤ a % suc n
m<1+a%n⇒m≤a%n {m} a n = k<1+a[modₕ]n⇒k≤a[modₕ]n 0 m a n

1+a%n≤1+m⇒a%n≤m : ∀ m a n → 0 < suc a % suc n → suc a % suc n ≤ suc m → a % suc n ≤ m
1+a%n≤1+m⇒a%n≤m m a n leq = 1+a[modₕ]n≤1+k⇒a[modₕ]n≤k 0 m a n leq

%-distribˡ-+ : ∀ a b n → (a + b) % suc n ≡ (a % suc n + b % suc n) % suc n
%-distribˡ-+ a b n-1 = begin-equality
  (a + b)                         % n ≡⟨ cong (λ v → (v + b) % n) (a≡a%n+[a/n]*n a n-1) ⟩
  (a % n +  a / n * n + b)        % n ≡⟨ cong (_% n) (+-assoc (a % n) _ b) ⟩
  (a % n + (a / n * n + b))       % n ≡⟨ cong (λ v → (a % n + v) % n) (+-comm _ b) ⟩
  (a % n + (b + a / n * n))       % n ≡⟨ cong (_% n) (sym (+-assoc (a % n) b _)) ⟩
  (a % n +  b + a / n * n)        % n ≡⟨ [a+kn]%n≡a%n (a % n + b) (a / n) n-1 ⟩
  (a % n +  b)                    % n ≡⟨ cong (λ v → (a % n + v) % n) (a≡a%n+[a/n]*n b n-1) ⟩
  (a % n + (b % n + (b / n) * n)) % n ≡⟨ sym (cong (_% n) (+-assoc (a % n) (b % n) _)) ⟩
  (a % n +  b % n + (b / n) * n)  % n ≡⟨ [a+kn]%n≡a%n (a % n + b % n) (b / n) n-1 ⟩
  (a % n +  b % n)                % n ∎
  where n = suc n-1

%-remove-+ˡ : ∀ a b {n} → suc n ∣ a → (a + b) % suc n ≡ b % suc n
%-remove-+ˡ a b {n-1} (divides p refl) = begin-equality
  (p * n + b) % n ≡⟨ cong (_% n) (+-comm (p * n) b) ⟩
  (b + p * n) % n ≡⟨ [a+kn]%n≡a%n b p n-1 ⟩
  b           % n ∎
  where n = suc n-1

%-remove-+ʳ : ∀ a b {n} → suc n ∣ b → (a + b) % suc n ≡ a % suc n
%-remove-+ʳ a b {n} eq rewrite +-comm a b = %-remove-+ˡ b a eq

------------------------------------------------------------------------
-- Properties of _/_

0/n≡0 : ∀ n .{≢0} → (0 / n) {≢0} ≡ 0
0/n≡0 (suc n-1) = refl

n/1≡a : ∀ n → n / 1 ≡ n
n/1≡a a = a[divₕ]1≡a 0 a

n/n≡1 : ∀ n .{≢0} → (n / n) {≢0} ≡ 1
n/n≡1 (suc n-1) = n[divₕ]n≡1 n-1 n-1

m*n/n≡m : ∀ m n .{≢0} → (m * n / n) {≢0} ≡ m
m*n/n≡m m (suc n-1) = a*n[divₕ]n≡a 0 m n-1

m/n*n≡m : ∀ {m n} .{≢0} → n ∣ m → (m / n) {≢0} * n ≡ m
m/n*n≡m {_} {n@(suc n-1)} (divides q refl) = cong (_* n) (m*n/n≡m q n)

n*[a/n]≡a : ∀ {a n} .{n≢0} → n ∣ a → n * (a / n) {n≢0} ≡ a
n*[a/n]≡a {n = n} n∣a = trans (*-comm n (_ / n)) (m/n*n≡m n∣a)

m/n*n≤m : ∀ m n .{≢0} → (m / n) {≢0} * n ≤ m
m/n*n≤m m n@(suc n-1) = begin
  (m / n) * n          ≤⟨ m≤m+n ((m / n) * n) (m % n) ⟩
  (m / n) * n + m % n  ≡⟨ +-comm _ (m % n) ⟩
  m % n + (m / n) * n  ≡⟨ sym (a≡a%n+[a/n]*n m n-1) ⟩
  m                    ∎

m/n<m : ∀ m n .{≢0} → m ≥ 1 → n ≥ 2 → (m / n) {≢0} < m
m/n<m m n@(suc n-1) m≥1 n≥2 = *-cancelʳ-< {n} (m / n) m (begin-strict
  (m / n) * n ≤⟨ m/n*n≤m m n ⟩
  m           <⟨ m<m*n m≥1 n≥2 ⟩
  m * n       ∎)

+-distrib-/ : ∀ m n {d} .{≢0} → (m % d) {≢0} + (n % d) {≢0} < d →
              ((m + n) / d) {≢0} ≡ (m / d) {≢0} + (n / d) {≢0}
+-distrib-/ m n {suc d-1} leq = +-distrib-divₕ 0 0 m n d-1 leq

+-distrib-/-∣ˡ : ∀ {m} n {d} .{≢0} → d ∣ m →
                 ((m + n) / d) {≢0} ≡ (m / d) {≢0} + (n / d) {≢0}
+-distrib-/-∣ˡ {m} n {d@(suc d-1)} (divides p refl) = +-distrib-/ m n (begin-strict
  p * d % d + n % d ≡⟨ cong (_+ n % d) (kn%n≡0 p d-1) ⟩
  n % d             <⟨ a%n<n n d-1 ⟩
  d                 ∎)

+-distrib-/-∣ʳ : ∀ {m} n {d} .{≢0} → d ∣ n →
                 ((m + n) / d) {≢0} ≡ (m / d) {≢0} + (n / d) {≢0}
+-distrib-/-∣ʳ {m} n {d@(suc d-1)} (divides p refl) = +-distrib-/ m n (begin-strict
  m % d + p * d % d ≡⟨ cong (m % d +_) (kn%n≡0 p d-1) ⟩
  m % d + 0         ≡⟨ +-identityʳ _ ⟩
  m % d             <⟨ a%n<n m d-1 ⟩
  suc d-1           ∎)

*-/-assoc : ∀ m {n d} {≢0} → d ∣ n → (m * n / d) {≢0} ≡ m * ((n / d) {≢0})
*-/-assoc zero    {_} {d@(suc d-1)} d∣n = 0/n≡0 (suc d)
*-/-assoc (suc m) {n} {d@(suc d-1)} d∣n = begin-equality
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

_div_ : (dividend divisor : ℕ) .{≢0 : False (divisor ≟ 0)} → ℕ
_div_ = _/_

_mod_ : (dividend divisor : ℕ) .{≢0 : False (divisor ≟ 0)} → Fin divisor
m mod (suc n) = fromℕ≤ (a%n<n m n)

_divMod_ : (dividend divisor : ℕ) .{≢0 : False (divisor ≟ 0)} →
           DivMod dividend divisor
m divMod n@(suc n-1) = result (m / n) (m mod n) (begin-equality
  m                                     ≡⟨ a≡a%n+[a/n]*n m n-1 ⟩
  m % n                      + [m/n]*n  ≡⟨ cong (_+ [m/n]*n) (sym (toℕ-fromℕ≤ (a%n<n m n-1))) ⟩
  toℕ (fromℕ≤ (a%n<n m n-1)) + [m/n]*n  ∎)
  where [m/n]*n = m / n * n
