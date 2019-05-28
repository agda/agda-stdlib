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

infixl 7 _/_ _%_

-- Natural division

_/_ : (dividend divisor : ℕ) .{≢0 : False (divisor ≟ 0)} → ℕ
a / (suc n) = div-helper 0 n a n

-- Natural remainder/modulus

_%_ : (dividend divisor : ℕ) .{≢0 : False (divisor ≟ 0)} → ℕ
a % (suc n) = mod-helper 0 n a n

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

0/n≡0 : ∀ n → 0 / suc n ≡ 0
0/n≡0 n = refl

a/1≡a : ∀ a → a / 1 ≡ a
a/1≡a a = a[divₕ]1≡a 0 a

n/n≡1 : ∀ n → suc n / suc n ≡ 1
n/n≡1 n = n[divₕ]n≡1 n n

a*n/n≡a : ∀ a n → a * suc n / suc n ≡ a
a*n/n≡a a n-1 = a*n[divₕ]n≡a 0 a n-1

a/n*n≤a : ∀ a n → a / suc n * suc n ≤ a
a/n*n≤a a n-1 = begin
  (a / n) * n          ≤⟨ m≤m+n ((a / n) * n) (a % n) ⟩
  (a / n) * n + a % n  ≡⟨ +-comm _ (a % n) ⟩
  a % n + (a / n) * n  ≡⟨ sym (a≡a%n+[a/n]*n a n-1) ⟩
  a                    ∎
  where n = suc n-1

a/n*n≡a : ∀ {a n} → suc n ∣ a → a / suc n * suc n ≡ a
a/n*n≡a {_} {n} (divides q refl) = cong (_* suc n) (a*n/n≡a q n)

+-distrib-/ : ∀ m n {d} → m % suc d + n % suc d < suc d →
              (m + n) / suc d ≡ m / suc d + n / suc d
+-distrib-/ m n {d = d} leq = +-distrib-divₕ 0 0 m n d leq

+-distrib-/-∣ˡ : ∀ {m} n {d} → suc d ∣ m →
              (m + n) / suc d ≡ m / suc d + n / suc d
+-distrib-/-∣ˡ {m} n {d} (divides p refl) = +-distrib-/ m n (begin-strict
  p * suc d % suc d + n % suc d ≡⟨ cong (_+ n % suc d) (kn%n≡0 p d) ⟩
  n % suc d                     <⟨ a%n<n n d ⟩
  suc d                         ∎)

+-distrib-/-∣ʳ : ∀ {m} n {d} → suc d ∣ n →
              (m + n) / suc d ≡ m / suc d + n / suc d
+-distrib-/-∣ʳ {m} n {d} (divides p refl) = +-distrib-/ m n (begin-strict
  m % suc d + p * suc d % suc d ≡⟨ cong (m % suc d +_) (kn%n≡0 p d) ⟩
  m % suc d + 0                 ≡⟨ +-identityʳ _ ⟩
  m % suc d                     <⟨ a%n<n m d ⟩
  suc d                         ∎)

*-/-assoc : ∀ m {n d} d≢0 → d ∣ n → (m * n / d) {d≢0} ≡ m * ((n / d) {d≢0})
*-/-assoc zero    {_} {suc d} d≢0 d∣n = 0/n≡0 d
*-/-assoc (suc m) {n} {suc d} d≢0 d∣n = begin-equality
  (n + m * n) / suc d         ≡⟨ +-distrib-/-∣ˡ _ d∣n ⟩
  n / suc d + (m * n) / suc d ≡⟨ cong (n / suc d +_) (*-/-assoc m d≢0 d∣n) ⟩
  n / suc d + m * (n / suc d) ∎

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
a mod (suc n) = fromℕ≤ (a%n<n a n)

_divMod_ : (dividend divisor : ℕ) .{≢0 : False (divisor ≟ 0)} →
           DivMod dividend divisor
a divMod (suc n) = result (a / suc n) (a mod suc n) (begin-equality
  a                                   ≡⟨ a≡a%n+[a/n]*n a n ⟩
  a % suc n                + [a/n]*n  ≡⟨ cong (_+ [a/n]*n) (sym (toℕ-fromℕ≤ (a%n<n a n))) ⟩
  toℕ (fromℕ≤ (a%n<n a n)) + [a/n]*n  ∎)
  where [a/n]*n = a / suc n * suc n
