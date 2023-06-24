------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural number division
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.DivMod where

open import Agda.Builtin.Nat using (div-helper; mod-helper)

open import Data.Fin.Base using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat.Base as Nat
open import Data.Nat.DivMod.Core
open import Data.Nat.Divisibility.Core
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Function.Base using (_$_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)

import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup as *-CS

open ≤-Reasoning

------------------------------------------------------------------------
-- Definitions

open import Data.Nat.Base public
  using (_%_; _/_)

------------------------------------------------------------------------
-- Relationship between _%_ and _div_

m≡m%n+[m/n]*n : ∀ m n .{{_ : NonZero n}} → m ≡ m % n + (m / n) * n
m≡m%n+[m/n]*n m (suc n) = div-mod-lemma 0 0 m n

m%n≡m∸m/n*n : ∀ m n .{{_ : NonZero n}} → m % n ≡ m ∸ (m / n) * n
m%n≡m∸m/n*n m n = begin-equality
  m % n                  ≡˘⟨ m+n∸n≡m (m % n) m/n*n ⟩
  m % n + m/n*n ∸ m/n*n  ≡˘⟨ cong (_∸ m/n*n) (m≡m%n+[m/n]*n m n) ⟩
  m ∸ m/n*n              ∎
  where m/n*n = (m / n) * n

------------------------------------------------------------------------
-- Properties of _%_

%-congˡ : ∀ {m n o} .⦃ _ : NonZero o ⦄ → m ≡ n → m % o ≡ n % o
%-congˡ refl = refl

%-congʳ : ∀ {m n o} .⦃ _ : NonZero m ⦄ .⦃ _ : NonZero n ⦄ → m ≡ n →
          o % m ≡ o % n
%-congʳ refl = refl

n%1≡0 : ∀ n → n % 1 ≡ 0
n%1≡0 = a[modₕ]1≡0

n%n≡0 : ∀ n .{{_ : NonZero n}} → n % n ≡ 0
n%n≡0 (suc n-1) = n[modₕ]n≡0 0 n-1

m%n%n≡m%n : ∀ m n .{{_ : NonZero n}} → m % n % n ≡ m % n
m%n%n≡m%n m (suc n-1) = modₕ-idem 0 m n-1

[m+n]%n≡m%n : ∀ m n .{{_ : NonZero n}} → (m + n) % n ≡ m % n
[m+n]%n≡m%n m (suc n-1) = a+n[modₕ]n≡a[modₕ]n 0 m n-1

[m+kn]%n≡m%n : ∀ m k n .{{_ : NonZero n}} → (m + k * n) % n ≡ m % n
[m+kn]%n≡m%n m zero    n = cong (_% n) (+-identityʳ m)
[m+kn]%n≡m%n m (suc k) n = begin-equality
  (m + (n + k * n)) % n ≡⟨ cong (_% n) (sym (+-assoc m n (k * n))) ⟩
  (m + n + k * n)   % n ≡⟨ [m+kn]%n≡m%n (m + n) k n ⟩
  (m + n)           % n ≡⟨ [m+n]%n≡m%n m n ⟩
  m                 % n ∎

m≤n⇒[n∸m]%m≡n%m : ∀ {m n} .⦃ _ : NonZero m ⦄ → m ≤ n →
                  (n ∸ m) % m ≡ n % m
m≤n⇒[n∸m]%m≡n%m {m} {n} m≤n = begin-equality
  (n ∸ m) % m     ≡˘⟨ [m+n]%n≡m%n (n ∸ m) m ⟩
  (n ∸ m + m) % m ≡⟨ cong (_% m) (m∸n+n≡m m≤n) ⟩
  n % m           ∎

m*n≤o⇒[o∸m*n]%n≡o%n : ∀ m {n o} .⦃ _ : NonZero n ⦄ → m * n ≤ o →
                      (o ∸ m * n) % n ≡ o % n
m*n≤o⇒[o∸m*n]%n≡o%n m {n} {o} m*n≤o = begin-equality
  (o ∸ m * n) % n         ≡˘⟨ [m+kn]%n≡m%n (o ∸ m * n) m n ⟩
  (o ∸ m * n + m * n) % n ≡⟨ cong (_% n) (m∸n+n≡m m*n≤o) ⟩
  o % n                   ∎

m∣n⇒o%n%m≡o%m : ∀ m n o .⦃ _ : NonZero m ⦄ .⦃ _ : NonZero n ⦄ → m ∣ n →
                o % n % m ≡ o % m
m∣n⇒o%n%m≡o%m m n o (divides p refl) = begin-equality
  o % pm % m               ≡⟨ %-congˡ (m%n≡m∸m/n*n o pm) ⟩
  (o ∸ o / pm * pm) % m    ≡˘⟨ cong (λ # → (o ∸ #) % m) (*-assoc (o / pm) p m) ⟩
  (o ∸ o / pm * p * m) % m ≡⟨ m*n≤o⇒[o∸m*n]%n≡o%n (o / pm * p) lem ⟩
  o % m                    ∎
  where
  pm = p * m

  lem : o / pm * p * m ≤ o
  lem = begin
    o / pm * p * m       ≡⟨ *-assoc (o / pm) p m ⟩
    -- Sort out dependencies in this file, then use m/n*n≤m instead.
    o / pm * pm          ≤⟨ m≤m+n (o / pm * pm) (o % pm) ⟩
    o / pm * pm + o % pm ≡⟨ +-comm _ (o % pm) ⟩
    o % pm + o / pm * pm ≡˘⟨ m≡m%n+[m/n]*n o pm ⟩
    o                    ∎

m*n%n≡0 : ∀ m n .{{_ : NonZero n}} → (m * n) % n ≡ 0
m*n%n≡0 m (suc n-1) = [m+kn]%n≡m%n 0 m (suc n-1)

m%n<n : ∀ m n .{{_ : NonZero n}} → m % n < n
m%n<n m (suc n-1) = s≤s (a[modₕ]n<n 0 m n-1)

m%n≤n : ∀ m n .{{_ : NonZero n}} → m % n ≤ n
m%n≤n m n = <⇒≤ (m%n<n m n)

m%n≤m : ∀ m n .{{_ : NonZero n}} → m % n ≤ m
m%n≤m m (suc n-1) = a[modₕ]n≤a 0 m n-1

m≤n⇒m%n≡m : ∀ {m n} → m ≤ n → m % suc n ≡ m
m≤n⇒m%n≡m {m} {n} m≤n with ≤⇒≤″ m≤n
... | less-than-or-equal {k} refl = a≤n⇒a[modₕ]n≡a 0 (m + k) m k

m<n⇒m%n≡m : ∀ {m n} .⦃ _ : NonZero n ⦄ → m < n → m % n ≡ m
m<n⇒m%n≡m {m} {suc n} m<n = m≤n⇒m%n≡m (<⇒≤pred m<n)

%-pred-≡0 : ∀ {m n} .{{_ : NonZero n}} → (suc m % n) ≡ 0 → (m % n) ≡ n ∸ 1
%-pred-≡0 {m} {suc n-1} eq = a+1[modₕ]n≡0⇒a[modₕ]n≡n-1 0 n-1 m eq

m<[1+n%d]⇒m≤[n%d] : ∀ {m} n d .{{_ : NonZero d}} → m < suc n % d → m ≤ n % d
m<[1+n%d]⇒m≤[n%d] {m} n (suc d-1) = k<1+a[modₕ]n⇒k≤a[modₕ]n 0 m n d-1

[1+m%d]≤1+n⇒[m%d]≤n : ∀ m n d .{{_ : NonZero d}} → 0 < suc m % d → suc m % d ≤ suc n → m % d ≤ n
[1+m%d]≤1+n⇒[m%d]≤n m n (suc d-1) leq = 1+a[modₕ]n≤1+k⇒a[modₕ]n≤k 0 n m d-1 leq

%-distribˡ-+ : ∀ m n d .{{_ : NonZero d}} → (m + n) % d ≡ ((m % d) + (n % d)) % d
%-distribˡ-+ m n d@(suc d-1) = begin-equality
  (m + n)                         % d ≡⟨ cong (λ v → (v + n) % d) (m≡m%n+[m/n]*n m d) ⟩
  (m % d +  m / d * d + n)        % d ≡⟨ cong (_% d) (+-assoc (m % d) _ n) ⟩
  (m % d + (m / d * d + n))       % d ≡⟨ cong (λ v → (m % d + v) % d) (+-comm _ n) ⟩
  (m % d + (n + m / d * d))       % d ≡⟨ cong (_% d) (sym (+-assoc (m % d) n _)) ⟩
  (m % d +  n + m / d * d)        % d ≡⟨ [m+kn]%n≡m%n (m % d + n) (m / d) d ⟩
  (m % d +  n)                    % d ≡⟨ cong (λ v → (m % d + v) % d) (m≡m%n+[m/n]*n n d) ⟩
  (m % d + (n % d + (n / d) * d)) % d ≡⟨ sym (cong (_% d) (+-assoc (m % d) (n % d) _)) ⟩
  (m % d +  n % d + (n / d) * d)  % d ≡⟨ [m+kn]%n≡m%n (m % d + n % d) (n / d) d ⟩
  (m % d +  n % d)                % d ∎

%-distribˡ-* : ∀ m n d .{{_ : NonZero d}} → (m * n) % d ≡ ((m % d) * (n % d)) % d
%-distribˡ-* m n d@(suc d-1) = begin-equality
  (m * n)                                             % d ≡⟨ cong (λ h → (h * n) % d) (m≡m%n+[m/n]*n m d) ⟩
  ((m′ + k * d) * n)                                  % d ≡⟨ cong (λ h → ((m′ + k * d) * h) % d) (m≡m%n+[m/n]*n n d) ⟩
  ((m′ + k * d) * (n′ + j * d))                       % d ≡⟨ cong (_% d) lemma ⟩
  (m′ * n′ + (m′ * j + (n′ + j * d) * k) * d)         % d ≡⟨ [m+kn]%n≡m%n (m′ * n′) (m′ * j + (n′ + j * d) * k) d ⟩
  (m′ * n′)                                           % d ≡⟨⟩
  ((m % d) * (n % d)) % d ∎
  where
  m′ = m % d
  n′ = n % d
  k  = m / d
  j  = n / d
  lemma : (m′ + k * d) * (n′ + j * d) ≡ m′ * n′ + (m′ * j + (n′ + j * d) * k) * d
  lemma = begin-equality
    (m′ + k * d) * (n′ + j * d)                       ≡⟨ *-distribʳ-+ (n′ + j * d) m′ (k * d) ⟩
    m′ * (n′ + j * d) + (k * d) * (n′ + j * d)        ≡⟨ cong₂ _+_ (*-distribˡ-+ m′ n′ (j * d)) (*-comm (k * d) (n′ + j * d)) ⟩
    (m′ * n′ + m′ * (j * d)) + (n′ + j * d) * (k * d) ≡⟨ +-assoc (m′ * n′) (m′ * (j * d)) ((n′ + j * d) * (k * d)) ⟩
    m′ * n′ + (m′ * (j * d) + (n′ + j * d) * (k * d)) ≡˘⟨ cong (m′ * n′ +_) (cong₂ _+_ (*-assoc m′ j d) (*-assoc (n′ + j * d) k d)) ⟩
    m′ * n′ + ((m′ * j) * d + ((n′ + j * d) * k) * d) ≡˘⟨ cong (m′ * n′ +_) (*-distribʳ-+ d (m′ * j) ((n′ + j * d) * k)) ⟩
    m′ * n′ + (m′ * j + (n′ + j * d) * k) * d         ∎

%-remove-+ˡ : ∀ {m} n {d} .{{_ : NonZero d}} → d ∣ m → (m + n) % d ≡ n % d
%-remove-+ˡ {m} n {d@(suc d-1)} (divides p refl) = begin-equality
  (p * d + n) % d ≡⟨ cong (_% d) (+-comm (p * d) n) ⟩
  (n + p * d) % d ≡⟨ [m+kn]%n≡m%n n p d ⟩
  n           % d ∎

%-remove-+ʳ : ∀ m {n d} .{{_ : NonZero d}} → d ∣ n → (m + n) % d ≡ m % d
%-remove-+ʳ m {n} {suc _} eq rewrite +-comm m n = %-remove-+ˡ {n} m eq

------------------------------------------------------------------------
-- Properties of _/_

/-congˡ : ∀ {m n o : ℕ} .{{_ : NonZero o}} →
          m ≡ n → m / o ≡ n / o
/-congˡ refl = refl

/-congʳ : ∀ {m n o : ℕ} .{{_ : NonZero n}} .{{_ : NonZero o}} →
          n ≡ o → m / n ≡ m / o
/-congʳ refl = refl

0/n≡0 : ∀ n .{{_ : NonZero n}} → 0 / n ≡ 0
0/n≡0 (suc n-1) = refl

n/1≡n : ∀ n → n / 1 ≡ n
n/1≡n n = a[divₕ]1≡a 0 n

n/n≡1 : ∀ n .{{_ : NonZero n}} → n / n ≡ 1
n/n≡1 (suc n-1) = n[divₕ]n≡1 n-1 n-1

m*n/n≡m : ∀ m n .{{_ : NonZero n}} → m * n / n ≡ m
m*n/n≡m m (suc n-1) = a*n[divₕ]n≡a 0 m n-1

m/n*n≡m : ∀ {m n} .{{_ : NonZero n}} → n ∣ m → m / n * n ≡ m
m/n*n≡m {_} {n@(suc n-1)} (divides q refl) = cong (_* n) (m*n/n≡m q n)

m*[n/m]≡n : ∀ {m n} .{{_ : NonZero m}} → m ∣ n → m * (n / m) ≡ n
m*[n/m]≡n {m} m∣n = trans (*-comm m (_ / m)) (m/n*n≡m m∣n)

m/n*n≤m : ∀ m n .{{_ : NonZero n}} → (m / n) * n ≤ m
m/n*n≤m m n@(suc n-1) = begin
  (m / n) * n          ≤⟨ m≤m+n ((m / n) * n) (m % n) ⟩
  (m / n) * n + m % n  ≡⟨ +-comm _ (m % n) ⟩
  m % n + (m / n) * n  ≡⟨ sym (m≡m%n+[m/n]*n m n) ⟩
  m                    ∎

m/n≤m : ∀ m n .{{_ : NonZero n}} → (m / n) ≤ m
m/n≤m m n = *-cancelʳ-≤ (m / n) m n (begin
  (m / n) * n ≤⟨ m/n*n≤m m n ⟩
  m           ≤⟨ m≤m*n m n ⟩
  m * n       ∎)

m/n<m : ∀ m n .{{_ : NonZero m}} .{{_ : NonZero n}} → n ≥ 2 → m / n < m
m/n<m m n n≥2 = *-cancelʳ-< _ (m / n) m (begin-strict
  (m / n) * n ≤⟨ m/n*n≤m m n ⟩
  m           <⟨ m<m*n m n n≥2 ⟩
  m * n       ∎)

/-mono-≤ : ∀ {m n o p} .{{_ : NonZero o}} .{{_ : NonZero p}} →
           m ≤ n → o ≥ p → m / o ≤ n / p
/-mono-≤ m≤n (s≤s o≥p) = divₕ-mono-≤ 0 m≤n o≥p

/-monoˡ-≤ : ∀ {m n} o .{{_ : NonZero o}} → m ≤ n → m / o ≤ n / o
/-monoˡ-≤ o m≤n = /-mono-≤ m≤n (≤-refl {o})

/-monoʳ-≤ : ∀ m {n o} .{{_ : NonZero n}} .{{_ : NonZero o}} →
            n ≥ o → m / n ≤ m / o
/-monoʳ-≤ m n≥o = /-mono-≤ ≤-refl n≥o

/-cancelʳ-≡ : ∀ {m n o} .{{_ : NonZero o}} →
              o ∣ m → o ∣ n → m / o ≡ n / o → m ≡ n
/-cancelʳ-≡ {m} {n} {o} o∣m o∣n m/o≡n/o = begin-equality
  m           ≡˘⟨ m*[n/m]≡n {o} {m} o∣m ⟩
  o * (m / o) ≡⟨  cong (o *_) m/o≡n/o ⟩
  o * (n / o) ≡⟨  m*[n/m]≡n {o} {n} o∣n ⟩
  n           ∎

m<n⇒m/n≡0 : ∀ {m n} .{{_ : NonZero n}} → m < n → m / n ≡ 0
m<n⇒m/n≡0 {m} {suc n-1} (s≤s m≤n) = divₕ-finish n-1 m n-1 m≤n

m≥n⇒m/n>0 : ∀ {m n} .{{_ : NonZero n}} → m ≥ n → m / n > 0
m≥n⇒m/n>0 {m@(suc _)} {n@(suc _)} m≥n = begin
  1     ≡⟨ sym (n/n≡1 m) ⟩
  m / m ≤⟨ /-monoʳ-≤ m m≥n ⟩
  m / n ∎

+-distrib-/ : ∀ m n {d} .{{_ : NonZero d}} → m % d + n % d < d →
              (m + n) / d ≡ m / d + n / d
+-distrib-/ m n {suc d-1} leq = +-distrib-divₕ 0 0 m n d-1 leq

+-distrib-/-∣ˡ : ∀ {m} n {d} .{{_ : NonZero d}} →
                 d ∣ m → (m + n) / d ≡ m / d + n / d
+-distrib-/-∣ˡ {m} n {d} (divides p refl) = +-distrib-/ m n (begin-strict
  p * d % d + n % d ≡⟨ cong (_+ n % d) (m*n%n≡0 p d) ⟩
  n % d             <⟨ m%n<n n d ⟩
  d                 ∎)

+-distrib-/-∣ʳ : ∀ m {n} {d} .{{_ : NonZero d}} →
                 d ∣ n → (m + n) / d ≡ m / d + n / d
+-distrib-/-∣ʳ m {n} {d} (divides p refl) = +-distrib-/ m n (begin-strict
  m % d + p * d % d ≡⟨ cong (m % d +_) (m*n%n≡0 p d) ⟩
  m % d + 0         ≡⟨ +-identityʳ _ ⟩
  m % d             <⟨ m%n<n m d ⟩
  d                 ∎)

m/n≡1+[m∸n]/n : ∀ {m n} .{{_ : NonZero n}} → m ≥ n → m / n ≡ 1 + ((m ∸ n) / n)
m/n≡1+[m∸n]/n {m@(suc m-1)} {n@(suc n-1)} m≥n = begin-equality
  m / n                              ≡⟨⟩
  div-helper 0 n-1 m n-1             ≡⟨ divₕ-restart n-1 m n-1 m≥n ⟩
  div-helper 1 n-1 (m ∸ n) n-1       ≡⟨ divₕ-extractAcc 1 n-1 (m ∸ n) n-1 ⟩
  1 + (div-helper 0 n-1 (m ∸ n) n-1) ≡⟨⟩
  1 + (m ∸ n) / n                    ∎

m*n/m*o≡n/o : ∀ m n o .{{_ : NonZero o}} .{{_ : NonZero (m * o)}} →
              (m * n) / (m * o) ≡ n / o
m*n/m*o≡n/o m@(suc m-1) n o = helper (<-wellFounded n)
  where
  helper : ∀ {n} → Acc _<_ n → (m * n) / (m * o) ≡ n / o
  helper {n} (acc rec) with n <? o
  ... | yes n<o = trans (m<n⇒m/n≡0 (*-monoʳ-< m n<o)) (sym (m<n⇒m/n≡0 n<o))
  ... | no  n≮o = begin-equality
    (m * n) / (m * o)             ≡⟨  m/n≡1+[m∸n]/n (*-monoʳ-≤ m (≮⇒≥ n≮o)) ⟩
    1 + (m * n ∸ m * o) / (m * o) ≡˘⟨ cong (λ v → 1 + v / (m * o)) (*-distribˡ-∸ m n o) ⟩
    1 + (m * (n ∸ o)) / (m * o)   ≡⟨  cong suc (helper (rec (n ∸ o) n∸o<n)) ⟩
    1 + (n ∸ o) / o               ≡˘⟨ cong₂ _+_ (n/n≡1 o) refl ⟩
    o / o + (n ∸ o) / o           ≡˘⟨ +-distrib-/-∣ˡ (n ∸ o) (divides 1 ((sym (*-identityˡ o)))) ⟩
    (o + (n ∸ o)) / o             ≡⟨  cong (_/ o) (m+[n∸m]≡n (≮⇒≥ n≮o)) ⟩
    n / o                         ∎
    where n∸o<n = ∸-monoʳ-< (n≢0⇒n>0 (≢-nonZero⁻¹ o)) (≮⇒≥ n≮o)

m*n/o*n≡m/o : ∀ m n o .⦃ _ : NonZero o ⦄ ⦃ _ : NonZero (o * n) ⦄ →
              m * n / (o * n) ≡ m / o
m*n/o*n≡m/o m n o ⦃ _ ⦄ ⦃ o*n≢0 ⦄ = begin-equality
  m * n / (o * n) ≡⟨ /-congˡ (*-comm m n) ⟩
  n * m / (o * n) ≡⟨ /-congʳ (*-comm o n) ⟩
  n * m / (n * o) ≡⟨ m*n/m*o≡n/o n m o ⟩
  m / o           ∎
  where instance n*o≢0 = subst NonZero (*-comm o n) o*n≢0

m<n*o⇒m/o<n : ∀ {m n o} .⦃ _ : NonZero o ⦄ → m < n * o → m / o < n
m<n*o⇒m/o<n {m} {suc n} {o} m<n*o with m <? o
... | yes m<o = begin-strict
  m / o ≡⟨ m<n⇒m/n≡0 m<o ⟩
  0     <⟨ z<s ⟩
  suc n ∎
... | no m≮o = begin-strict
  m / o             ≡⟨ m/n≡1+[m∸n]/n (≮⇒≥ m≮o) ⟩
  suc ((m ∸ o) / o) <⟨ s≤s (m<n*o⇒m/o<n lem) ⟩
  suc n             ∎
  where
  lem : m ∸ o < n * o
  lem = begin-strict
    m ∸ o         <⟨ ∸-monoˡ-< m<n*o (≮⇒≥ m≮o) ⟩
    o + n * o ∸ o ≡⟨ m+n∸m≡n o (n * o) ⟩
    n * o         ∎

[m∸n]/n≡m/n∸1 : ∀ m n .⦃ _ : NonZero n ⦄ → (m ∸ n) / n ≡ pred (m / n)
[m∸n]/n≡m/n∸1 m n with m <? n
... | yes m<n = begin-equality
  (m ∸ n) / n  ≡⟨ m<n⇒m/n≡0 (<-transʳ (m∸n≤m m n) m<n) ⟩
  0            ≡⟨⟩
  0 ∸ 1        ≡˘⟨ cong (_∸ 1) (m<n⇒m/n≡0 m<n) ⟩
  m / n ∸ 1    ≡⟨⟩
  pred (m / n) ∎
... | no m≮n = begin-equality
  (m ∸ n) / n           ≡⟨⟩
  suc ((m ∸ n) / n) ∸ 1 ≡˘⟨ cong (_∸ 1) (m/n≡1+[m∸n]/n (≮⇒≥ m≮n)) ⟩
  m / n ∸ 1             ≡⟨⟩
  pred (m / n)          ∎

[m∸n*o]/o≡m/o∸n : ∀ m n o .⦃ _ : NonZero o ⦄ → (m ∸ n * o) / o ≡ m / o ∸ n
[m∸n*o]/o≡m/o∸n m zero    o = refl
[m∸n*o]/o≡m/o∸n m (suc n) o = begin-equality
  (m ∸ (o + n * o)) / o ≡˘⟨ /-congˡ (∸-+-assoc m o (n * o)) ⟩
  (m ∸ o ∸ n * o) / o   ≡⟨ [m∸n*o]/o≡m/o∸n (m ∸ o) n o ⟩
  (m ∸ o) / o ∸ n       ≡⟨ cong (_∸ n) ([m∸n]/n≡m/n∸1 m o) ⟩
  m / o ∸ 1 ∸ n         ≡⟨ ∸-+-assoc (m / o) 1 n ⟩
  m / o ∸ suc n         ∎

m/n/o≡m/[n*o] : ∀ m n o .⦃ _ : NonZero n ⦄ .⦃ _ : NonZero o ⦄
                .⦃ _ : NonZero (n * o) ⦄ → m / n / o ≡ m / (n * o)
m/n/o≡m/[n*o] m n o = begin-equality
  m / n / o                             ≡⟨ /-congˡ {o = o} (/-congˡ (m≡m%n+[m/n]*n m n*o)) ⟩
  (m % n*o + m / n*o * n*o) / n / o     ≡⟨ /-congˡ (+-distrib-/-∣ʳ (m % n*o) lem₁) ⟩
  (m % n*o / n + m / n*o * n*o / n) / o ≡⟨ cong (λ # → (m % n*o / n + #) / o) lem₂ ⟩
  (m % n*o / n + m / n*o * o) / o       ≡⟨ +-distrib-/-∣ʳ (m % n*o / n) (divides (m / n*o) refl) ⟩
  m % n*o / n / o + m / n*o * o / o     ≡⟨ cong (m % n*o / n / o +_) (m*n/n≡m (m / n*o) o) ⟩
  m % n*o / n / o + m / n*o             ≡⟨ cong (_+ m / n*o) (m<n⇒m/n≡0 (m<n*o⇒m/o<n {n = o} lem₃)) ⟩
  m / n*o                               ∎
  where
  n*o = n * o
  o*n = o * n

  lem₁ : n ∣ m / n*o * n*o
  lem₁ = divides (m / n*o * o) $ begin-equality
    m / n*o * n*o   ≡⟨ cong (m / n*o *_) (*-comm n o) ⟩
    m / n*o * o*n   ≡˘⟨ *-assoc (m / n*o) o n ⟩
    m / n*o * o * n ∎

  lem₂ : m / n*o * n*o / n ≡ m / n*o * o
  lem₂ = begin-equality
    m / n*o * n*o / n   ≡⟨ cong (λ # → m / n*o * # / n) (*-comm n o) ⟩
    m / n*o * o*n / n   ≡˘⟨ /-congˡ (*-assoc (m / n*o) o n) ⟩
    m / n*o * o * n / n ≡⟨ m*n/n≡m (m / n*o * o) n ⟩
    m / n*o * o         ∎

  lem₃ : m % n*o < o*n
  lem₃ = begin-strict
    m % n*o <⟨ m%n<n m n*o ⟩
    n*o     ≡⟨ *-comm n o ⟩
    o*n     ∎

*-/-assoc : ∀ m {n d} .{{_ : NonZero d}} → d ∣ n → m * n / d ≡ m * (n / d)
*-/-assoc zero    {_} {d@(suc _)} d∣n = 0/n≡0 (suc d)
*-/-assoc (suc m) {n} {d@(suc _)} d∣n = begin-equality
  (n + m * n) / d     ≡⟨ +-distrib-/-∣ˡ _ d∣n ⟩
  n / d + (m * n) / d ≡⟨ cong (n / d +_) (*-/-assoc m d∣n) ⟩
  n / d + m * (n / d) ∎

/-*-interchange : ∀ {m n o p} .{{_ : NonZero o}} .{{_ : NonZero p}} .{{_ : NonZero (o * p)}} →
                  o ∣ m → p ∣ n → (m * n) / (o * p) ≡ (m / o) * (n / p)
/-*-interchange {m} {n} {o@(suc _)} {p@(suc _)} o∣m p∣n = *-cancelˡ-≡ _ _ (o * p) (begin-equality
  (o * p) * ((m * n) / (o * p)) ≡⟨  m*[n/m]≡n (*-pres-∣ o∣m p∣n) ⟩
  m * n                         ≡˘⟨ cong₂ _*_ (m*[n/m]≡n o∣m) (m*[n/m]≡n p∣n) ⟩
  (o * (m / o)) * (p * (n / p)) ≡⟨ [m*n]*[o*p]≡[m*o]*[n*p] o (m / o) p (n / p) ⟩
  (o * p) * ((m / o) * (n / p)) ∎)

m*n/m!≡n/[m∸1]! : ∀ m n .{{_ : NonZero m}} →
                 (m * n / m !) {{m !≢0}}  ≡ (n / (pred m) !) {{pred m !≢0}}
m*n/m!≡n/[m∸1]! (suc m) n = m*n/m*o≡n/o (suc m) n (m !) {{m !≢0}} {{suc m !≢0}}

m%[n*o]/o≡m/o%n : ∀ m n o .⦃ _ : NonZero n ⦄ .⦃ _ : NonZero o ⦄
                  ⦃ _ : NonZero (n * o) ⦄ → m % (n * o) / o ≡ m / o % n
m%[n*o]/o≡m/o%n m n o ⦃ _ ⦄ ⦃ _ ⦄ ⦃ n*o≢0 ⦄ = begin-equality
  m % (n * o) / o                   ≡⟨ /-congˡ (m%n≡m∸m/n*n m (n * o)) ⟩
  (m ∸ (m / (n * o) * (n * o))) / o ≡˘⟨ cong (λ # → (m ∸ #) / o) (*-assoc (m / (n * o)) n o) ⟩
  (m ∸ (m / (n * o) * n * o)) / o   ≡⟨ [m∸n*o]/o≡m/o∸n m (m / (n * o) * n) o ⟩
  m / o ∸ m / (n * o) * n           ≡⟨ cong (λ # → m / o ∸ # * n) (/-congʳ (*-comm n o)) ⟩
  m / o ∸ m / (o * n) * n           ≡˘⟨ cong (λ # → m / o ∸ # * n) (m/n/o≡m/[n*o] m o n ) ⟩
  m / o ∸ m / o / n * n             ≡˘⟨ m%n≡m∸m/n*n (m / o) n ⟩
  m / o % n                         ∎
  where instance o*n≢0 = subst NonZero (*-comm n o) n*o≢0

m%n*o≡m*o%[n*o] : ∀ m n o .⦃ _ : NonZero n ⦄ ⦃ _ : NonZero (n * o) ⦄ →
                  m % n * o ≡ m * o % (n * o)
m%n*o≡m*o%[n*o] m n o ⦃ _ ⦄ ⦃ n*o≢0 ⦄ = begin-equality
  m % n * o                         ≡⟨ cong (_* o) (m%n≡m∸m/n*n m n) ⟩
  (m ∸ m / n * n) * o               ≡⟨ *-distribʳ-∸ o m (m / n * n) ⟩
  m * o ∸ m / n * n * o             ≡˘⟨ cong (λ # → m * o ∸ # * n * o) (m*n/o*n≡m/o m o n) ⟩
  m * o ∸ m * o / (n * o) * n * o   ≡⟨ cong (m * o ∸_) (*-assoc (m * o / (n * o)) n o) ⟩
  m * o ∸ m * o / (n * o) * (n * o) ≡˘⟨ m%n≡m∸m/n*n (m * o) (n * o) ⟩
  m * o % (n * o)                   ∎

[m*n+o]%[p*n]≡[m*n]%[p*n]+o : ∀ m {n o} p ⦃ _ : NonZero (p * n) ⦄ → o < n →
                              (m * n + o) % (p * n) ≡ (m * n) % (p * n) + o
[m*n+o]%[p*n]≡[m*n]%[p*n]+o m {n} {o} p@(suc p-1) ⦃ p*n≢0 ⦄ o<n = begin-equality
  (mn + o) % pn           ≡⟨ %-distribˡ-+ mn o pn ⟩
  (mn % pn + o % pn) % pn ≡⟨ cong (λ # → (mn % pn + #) % pn) (m<n⇒m%n≡m (m<n⇒m<o*n p o<n)) ⟩
  (mn % pn + o) % pn      ≡⟨ m<n⇒m%n≡m lem₂ ⟩
  mn % pn + o             ∎
  where
  mn = m * n
  pn = p * n

  lem₁ : mn % pn ≤ p-1 * n
  lem₁ = begin
    mn % pn     ≡˘⟨ m%n*o≡m*o%[n*o] m p n ⟩
    (m % p) * n ≤⟨ *-monoˡ-≤ n (m<1+n⇒m≤n (m%n<n m p)) ⟩
    p-1 * n     ∎

  lem₂ : mn % pn + o < pn
  lem₂ = begin-strict
    mn % pn + o <⟨ +-mono-≤-< lem₁ o<n ⟩
    p-1 * n + n ≡⟨ +-comm (p-1 * n) n ⟩
    pn          ∎

------------------------------------------------------------------------
--  A specification of integer division.

record DivMod (dividend divisor : ℕ) : Set where
  constructor result
  field
    quotient  : ℕ
    remainder : Fin divisor
    property  : dividend ≡ toℕ remainder + quotient * divisor

infixl 7 _div_ _mod_ _divMod_

_div_ : (dividend divisor : ℕ) .{{_ : NonZero divisor}} → ℕ
_div_ = _/_

_mod_ : (dividend divisor : ℕ) .{{_ : NonZero divisor}} → Fin divisor
m mod (suc n) = fromℕ< (m%n<n m (suc n))

_divMod_ : (dividend divisor : ℕ) .{{_ : NonZero divisor}} →
           DivMod dividend divisor
m divMod n@(suc n-1) = result (m / n) (m mod n) (begin-equality
  m                                   ≡⟨  m≡m%n+[m/n]*n m n ⟩
  m % n                    + [m/n]*n  ≡˘⟨ cong (_+ [m/n]*n) (toℕ-fromℕ< (m%n<n m n)) ⟩
  toℕ (fromℕ< (m%n<n m n)) + [m/n]*n  ∎)
  where [m/n]*n = m / n * n
