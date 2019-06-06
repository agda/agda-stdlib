------------------------------------------------------------------------
-- The Agda standard library
--
-- Divisibility
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Divisibility where

open import Algebra
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Product
open import Function
open import Function.Equivalence using (_⇔_; equivalence)
open import Level using (0ℓ)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
import Relation.Binary.Reasoning.PartialOrder as POR
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

------------------------------------------------------------------------
-- Definition

open import Data.Nat.Divisibility.Core public

------------------------------------------------------------------------
-- Relationship with _%_

m%n≡0⇒n∣m : ∀ m n → m % suc n ≡ 0 → suc n ∣ m
m%n≡0⇒n∣m m n eq = divides (m / suc n) (begin-equality
  m                               ≡⟨ a≡a%n+[a/n]*n m n ⟩
  m % suc n + m / suc n * (suc n) ≡⟨ cong₂ _+_ eq refl ⟩
  m / suc n * (suc n)             ∎)
  where open ≤-Reasoning

n∣m⇒m%n≡0 : ∀ m n → suc n ∣ m → m % suc n ≡ 0
n∣m⇒m%n≡0 m n (divides v eq) = begin-equality
  m           % suc n  ≡⟨ cong (_% suc n) eq ⟩
  (v * suc n) % suc n  ≡⟨ kn%n≡0 v n ⟩
  0                    ∎
  where open ≤-Reasoning

m%n≡0⇔n∣m : ∀ m n → m % suc n ≡ 0 ⇔ suc n ∣ m
m%n≡0⇔n∣m m n = equivalence (m%n≡0⇒n∣m m n) (n∣m⇒m%n≡0 m n)

------------------------------------------------------------------------
-- _∣_ is a partial order

∣⇒≤ : ∀ {m n} → m ∣ suc n → m ≤ suc n
∣⇒≤ {m} {n} (divides (suc q) eq) = begin
  m          ≤⟨ m≤m+n m (q * m) ⟩
  suc q * m  ≡⟨ sym eq ⟩
  suc n      ∎
  where open ≤-Reasoning

∣-reflexive : _≡_ ⇒ _∣_
∣-reflexive {n} refl = divides 1 (sym (*-identityˡ n))

∣-refl : Reflexive _∣_
∣-refl = ∣-reflexive refl

∣-trans : Transitive _∣_
∣-trans (divides p refl) (divides q refl) =
  divides (q * p) (sym (*-assoc q p _))

∣-antisym : Antisymmetric _≡_ _∣_
∣-antisym {m}     {zero}  _ (divides q refl) = *-zeroʳ q
∣-antisym {zero}  {n}     (divides p eq) _   = sym (trans eq (*-comm p 0))
∣-antisym {suc m} {suc n} p∣q           q∣p  = ≤-antisym (∣⇒≤ p∣q) (∣⇒≤ q∣p)

infix 4 _∣?_

_∣?_ : Decidable _∣_
zero  ∣? zero   = yes (divides 0 refl)
zero  ∣? suc m  = no ((λ()) ∘′ ∣-antisym (divides 0 refl))
suc n ∣? m      = Dec.map (m%n≡0⇔n∣m m n) (m % suc n ≟ 0)

∣-isPreorder : IsPreorder _≡_ _∣_
∣-isPreorder = record
  { isEquivalence = PropEq.isEquivalence
  ; reflexive     = ∣-reflexive
  ; trans         = ∣-trans
  }

∣-isPartialOrder : IsPartialOrder _≡_ _∣_
∣-isPartialOrder = record
  { isPreorder = ∣-isPreorder
  ; antisym    = ∣-antisym
  }

∣-preorder : Preorder 0ℓ 0ℓ 0ℓ
∣-preorder = record
  { isPreorder = ∣-isPreorder
  }

∣-poset : Poset 0ℓ 0ℓ 0ℓ
∣-poset = record
  { isPartialOrder = ∣-isPartialOrder
  }

------------------------------------------------------------------------
-- A reasoning module for the _∣_ relation

module ∣-Reasoning = POR ∣-poset
  hiding   (_≈⟨_⟩_; _≈˘⟨_⟩_; _<⟨_⟩_)
  renaming (_≤⟨_⟩_ to _∣⟨_⟩_)

------------------------------------------------------------------------
-- Simple properties of _∣_

infix 10 1∣_ _∣0

1∣_ : ∀ n → 1 ∣ n
1∣ n = divides n (sym (*-identityʳ n))

_∣0 : ∀ n → n ∣ 0
n ∣0 = divides 0 refl

0∣⇒≡0 : ∀ {n} → 0 ∣ n → n ≡ 0
0∣⇒≡0 {n} 0∣n = ∣-antisym (n ∣0) 0∣n

∣1⇒≡1 : ∀ {n} → n ∣ 1 → n ≡ 1
∣1⇒≡1 {n} n∣1 = ∣-antisym n∣1 (1∣ n)

n∣n : ∀ {n} → n ∣ n
n∣n {n} = ∣-refl

------------------------------------------------------------------------
-- Properties of _∣_ and _+_

∣m∣n⇒∣m+n : ∀ {i m n} → i ∣ m → i ∣ n → i ∣ m + n
∣m∣n⇒∣m+n (divides p refl) (divides q refl) =
  divides (p + q) (sym (*-distribʳ-+ _ p q))

∣m+n∣m⇒∣n : ∀ {i m n} → i ∣ m + n → i ∣ m → i ∣ n
∣m+n∣m⇒∣n {i} {m} {n} (divides p m+n≡p*i) (divides q m≡q*i) =
  divides (p ∸ q) $ begin-equality
    n             ≡⟨ sym (m+n∸n≡m n m) ⟩
    n + m ∸ m     ≡⟨ cong (_∸ m) (+-comm n m) ⟩
    m + n ∸ m     ≡⟨ cong₂ _∸_ m+n≡p*i m≡q*i ⟩
    p * i ∸ q * i ≡⟨ sym (*-distribʳ-∸ i p q) ⟩
    (p ∸ q) * i   ∎
  where open ∣-Reasoning

------------------------------------------------------------------------
-- Properties of _∣_ and _*_

n∣m*n : ∀ m {n} → n ∣ m * n
n∣m*n m = divides m refl

m∣m*n : ∀ {m} n → m ∣ m * n
m∣m*n n = divides n (*-comm _ n)

∣m⇒∣m*n : ∀ {i m} n → i ∣ m → i ∣ m * n
∣m⇒∣m*n {i} {m} n (divides q refl) = ∣-trans (n∣m*n q) (m∣m*n n)

∣n⇒∣m*n : ∀ {i} m {n} → i ∣ n → i ∣ m * n
∣n⇒∣m*n {i} m {n} i∣n = subst (i ∣_) (*-comm n m) (∣m⇒∣m*n m i∣n)

*-monoʳ-∣ : ∀ {i j} k → i ∣ j → k * i ∣ k * j
*-monoʳ-∣ {i} {j} k (divides q refl) = divides q $ begin-equality
  k * (q * i)  ≡⟨ sym (*-assoc k q i) ⟩
  (k * q) * i  ≡⟨ cong (_* i) (*-comm k q) ⟩
  (q * k) * i  ≡⟨ *-assoc q k i ⟩
  q * (k * i)  ∎
  where open ≤-Reasoning

*-cancelˡ-∣ : ∀ {i j} k → suc k * i ∣ suc k * j → i ∣ j
*-cancelˡ-∣ {i} {j} k (divides q eq) =
  divides q $ *-cancelʳ-≡ j (q * i) $ begin-equality
    j * (suc k)      ≡⟨ *-comm j (suc k) ⟩
    suc k * j        ≡⟨ eq ⟩
    q * (suc k * i)  ≡⟨ cong (q *_) (*-comm (suc k) i) ⟩
    q * (i * suc k)  ≡⟨ sym (*-assoc q i (suc k)) ⟩
    (q * i) * suc k  ∎
    where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of _∣_ and _∸_

∣m∸n∣n⇒∣m : ∀ i {m n} → n ≤ m → i ∣ m ∸ n → i ∣ n → i ∣ m
∣m∸n∣n⇒∣m i {m} {n} n≤m (divides p m∸n≡p*i) (divides q n≡q*o) =
  divides (p + q) $ begin-equality
    m             ≡⟨ sym (m+[n∸m]≡n n≤m) ⟩
    n + (m ∸ n)   ≡⟨ +-comm n (m ∸ n) ⟩
    m ∸ n + n     ≡⟨ cong₂ _+_ m∸n≡p*i n≡q*o ⟩
    p * i + q * i ≡⟨ sym (*-distribʳ-+ i p q)  ⟩
    (p + q) * i   ∎
  where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of _∣_ and _/_

m/n∣m : ∀ {m n ≢0} → n ∣ m → (m / n) {≢0} ∣ m
m/n∣m {m} {n} (divides p refl) = begin
  p * n / n ≡⟨ m*n/n≡m p n ⟩
  p         ∣⟨ m∣m*n n ⟩
  p * n     ∎
  where open ∣-Reasoning

------------------------------------------------------------------------
-- Properties of _∣_ and _%_

∣n∣m%n⇒∣m : ∀ {m n d ≢0} → d ∣ n → d ∣ (m % n) {≢0} → d ∣ m
∣n∣m%n⇒∣m {m} {n@(suc n-1)} {d} (divides a n≡ad) (divides b m%n≡bd) =
  divides (b + (m / n) * a) (begin-equality
    m                         ≡⟨ a≡a%n+[a/n]*n m n-1 ⟩
    m % n + (m / n) * n       ≡⟨ cong₂ _+_ m%n≡bd (cong (m / n *_) n≡ad) ⟩
    b * d + (m / n) * (a * d) ≡⟨ sym (cong (b * d +_) (*-assoc (m / n) a d)) ⟩
    b * d + ((m / n) * a) * d ≡⟨ sym (*-distribʳ-+ d b _) ⟩
    (b + (m / n) * a) * d     ∎)
    where open ≤-Reasoning

%-presˡ-∣ : ∀ {m n d ≢0} → d ∣ m → d ∣ n → d ∣ (m % n) {≢0}
%-presˡ-∣ {m} {n@(suc n-1)} {d} (divides a refl) (divides b 1+n≡bd) =
  divides (a ∸ ad/n * b) $ begin-equality
    a * d % n              ≡⟨ a%n=a∸a/n*n (a * d) n-1 ⟩
    a * d ∸ ad/n * n       ≡⟨ cong (λ v → a * d ∸ ad/n * v) 1+n≡bd ⟩
    a * d ∸ ad/n * (b * d) ≡⟨ sym (cong (a * d ∸_) (*-assoc ad/n b d)) ⟩
    a * d ∸ (ad/n * b) * d ≡⟨ sym (*-distribʳ-∸ d a (ad/n * b)) ⟩
    (a ∸ ad/n * b) * d     ∎
  where open ≤-Reasoning; ad/n = a * d / n

------------------------------------------------------------------------
-- DEPRECATED - please use new names as continuing support for the old
-- names is not guaranteed.

-- Version 0.14

∣-+ = ∣m∣n⇒∣m+n
{-# WARNING_ON_USAGE ∣-+
"Warning: ∣-+ was deprecated in v0.14.
Please use ∣m∣n⇒∣m+n instead."
#-}
∣-∸ = ∣m+n∣m⇒∣n
{-# WARNING_ON_USAGE ∣-∸
"Warning: ∣-∸ was deprecated in v0.14.
Please use ∣m+n∣m⇒∣n instead."
#-}
∣-* = n∣m*n
{-# WARNING_ON_USAGE ∣-*
"Warning: ∣-* was deprecated in v0.14.
Please use n∣m*n instead."
#-}

-- Version 0.17

open import Data.Fin using (Fin; zero; suc; toℕ)
import Data.Fin.Properties as FP
open import Data.Nat.Solver
open +-*-Solver

nonZeroDivisor-lemma : ∀ m q (r : Fin (1 + m)) → toℕ r ≢ 0 →
                       1 + m ∤ toℕ r + q * (1 + m)
nonZeroDivisor-lemma m zero r r≢zero (divides zero eq) = r≢zero $ begin-equality
  toℕ r      ≡⟨ sym (*-identityˡ (toℕ r)) ⟩
  1 * toℕ r  ≡⟨ eq ⟩
  0          ∎
  where open ≤-Reasoning
nonZeroDivisor-lemma m zero r r≢zero (divides (suc q) eq) =
  m+1+n≰m m $ begin
    m + suc (q * suc m) ≡⟨ +-suc m (q * suc m) ⟩
    suc (m + q * suc m) ≡⟨ sym eq ⟩
    1 * toℕ r           ≡⟨ *-identityˡ (toℕ r) ⟩
    toℕ r               ≤⟨ FP.toℕ≤pred[n] r ⟩
    m                   ∎
    where open ≤-Reasoning
nonZeroDivisor-lemma m (suc q) r r≢zero d =
  nonZeroDivisor-lemma m q r r≢zero (∣m+n∣m⇒∣n d' ∣-refl)
  where
  lem = solve 3 (λ m r q → r :+ (m :+ q)  :=  m :+ (r :+ q))
                refl (suc m) (toℕ r) (q * suc m)
  d' = subst (1 + m ∣_) lem d
{-# WARNING_ON_USAGE nonZeroDivisor-lemma
"Warning: nonZeroDivisor-lemma was deprecated in v0.17."
#-}

-- Version 1.1

poset = ∣-poset
{-# WARNING_ON_USAGE poset
"Warning: poset was deprecated in v0.14.
Please use ∣-poset instead."
#-}
*-cong = *-monoʳ-∣
{-# WARNING_ON_USAGE *-cong
"Warning: *-cong was deprecated in v0.14.
Please use *-monoʳ-∣ instead."
#-}
/-cong = *-cancelˡ-∣
{-# WARNING_ON_USAGE /-cong
"Warning: /-cong was deprecated in v0.14.
Please use *-cancelˡ-∣ instead."
#-}
