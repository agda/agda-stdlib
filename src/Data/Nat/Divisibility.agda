------------------------------------------------------------------------
-- The Agda standard library
--
-- Divisibility
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Divisibility where

open import Algebra
open import Data.Nat.Base
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Function.Base using (_∘′_; _$_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (0ℓ)
open import Relation.Nullary.Decidable as Dec using (yes; no)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Bundles using (Preorder; Poset)
open import Relation.Binary.Structures
  using (IsPreorder; IsPartialOrder)
open import Relation.Binary.Definitions
  using (Reflexive; Transitive; Antisymmetric; Decidable)
import Relation.Binary.Reasoning.Preorder as PreorderReasoning
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.Reasoning.Syntax
import Relation.Binary.PropositionalEquality.Properties as PropEq

------------------------------------------------------------------------
-- Definition

open import Data.Nat.Divisibility.Core public

------------------------------------------------------------------------
-- Relationship with _%_

m%n≡0⇒n∣m : ∀ m n .{{_ : NonZero n}} → m % n ≡ 0 → n ∣ m
m%n≡0⇒n∣m m n eq = divides (m / n) (begin-equality
  m                  ≡⟨ m≡m%n+[m/n]*n m n ⟩
  m % n + m / n * n  ≡⟨ cong₂ _+_ eq refl ⟩
  m / n * n          ∎)
  where open ≤-Reasoning

n∣m⇒m%n≡0 : ∀ m n .{{_ : NonZero n}} → n ∣ m → m % n ≡ 0
n∣m⇒m%n≡0 .(q * n) n (divides-refl q) = m*n%n≡0 q n

m%n≡0⇔n∣m : ∀ m n .{{_ : NonZero n}} → m % n ≡ 0 ⇔ n ∣ m
m%n≡0⇔n∣m m n = mk⇔ (m%n≡0⇒n∣m m n) (n∣m⇒m%n≡0 m n)

------------------------------------------------------------------------
-- Properties of _∣_ and _≤_

∣⇒≤ : ∀ {m n} .{{_ : NonZero n}} → m ∣ n → m ≤ n
∣⇒≤ {m} {n@(suc _)} (divides (suc q) eq) = begin
  m          ≤⟨ m≤m+n m (q * m) ⟩
  suc q * m  ≡⟨ sym eq ⟩
  n          ∎
  where open ≤-Reasoning

>⇒∤ : ∀ {m n} .{{_ : NonZero n}} → m > n → m ∤ n
>⇒∤ (s≤s m>n) m∣n = contradiction (∣⇒≤ m∣n) (≤⇒≯ m>n)

------------------------------------------------------------------------
-- _∣_ is a partial order

-- these could/should inherit from Algebra.Properties.Monoid.Divisibility

∣-reflexive : _≡_ ⇒ _∣_
∣-reflexive {n} refl = divides 1 (sym (*-identityˡ n))

∣-refl : Reflexive _∣_
∣-refl = ∣-reflexive refl

∣-trans : Transitive _∣_
∣-trans (divides-refl p) (divides-refl q) =
  divides (q * p) (sym (*-assoc q p _))

∣-antisym : Antisymmetric _≡_ _∣_
∣-antisym {m}     {zero}  _ (divides-refl q) = *-zeroʳ q
∣-antisym {zero}  {n}     (divides p eq) _   = sym (trans eq (*-comm p 0))
∣-antisym {suc m} {suc n} p∣q           q∣p  = ≤-antisym (∣⇒≤ p∣q) (∣⇒≤ q∣p)

infix 4 _∣?_

_∣?_ : Decidable _∣_
zero  ∣? zero   = yes (divides-refl 0)
zero  ∣? suc m  = no ((λ()) ∘′ ∣-antisym (divides-refl 0))
suc n ∣? m      = Dec.map (m%n≡0⇔n∣m m (suc n)) (m % suc n ≟ 0)

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

module ∣-Reasoning where
  private module Base = PreorderReasoning ∣-preorder

  open Base public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨; step-∼; step-≲)
    renaming (≲-go to ∣-go)

  open ∣-syntax _IsRelatedTo_ _IsRelatedTo_ ∣-go public

------------------------------------------------------------------------
-- Simple properties of _∣_

infix 10 1∣_ _∣0

1∣_ : ∀ n → 1 ∣ n
1∣ n = divides n (sym (*-identityʳ n))

_∣0 : ∀ n → n ∣ 0
n ∣0 = divides-refl 0

0∣⇒≡0 : ∀ {n} → 0 ∣ n → n ≡ 0
0∣⇒≡0 {n} 0∣n = ∣-antisym (n ∣0) 0∣n

∣1⇒≡1 : ∀ {n} → n ∣ 1 → n ≡ 1
∣1⇒≡1 {n} n∣1 = ∣-antisym n∣1 (1∣ n)

n∣n : ∀ {n} → n ∣ n
n∣n {n} = ∣-refl

------------------------------------------------------------------------
-- Properties of _∣_ and _+_

∣m∣n⇒∣m+n : ∀ {i m n} → i ∣ m → i ∣ n → i ∣ m + n
∣m∣n⇒∣m+n (divides-refl p) (divides-refl q) =
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

n∣m*n*o : ∀ m {n} o → n ∣ m * n * o
n∣m*n*o m o = ∣-trans (n∣m*n m) (m∣m*n o)

∣m⇒∣m*n : ∀ {i m} n → i ∣ m → i ∣ m * n
∣m⇒∣m*n {i} {m} n (divides-refl q) = ∣-trans (n∣m*n q) (m∣m*n n)

∣n⇒∣m*n : ∀ {i} m {n} → i ∣ n → i ∣ m * n
∣n⇒∣m*n m {n} rewrite *-comm m n = ∣m⇒∣m*n m

m*n∣⇒m∣ : ∀ {i} m n → m * n ∣ i → m ∣ i
m*n∣⇒m∣ m n (divides-refl q) = ∣n⇒∣m*n q (m∣m*n n)

m*n∣⇒n∣ : ∀ {i} m n → m * n ∣ i → n ∣ i
m*n∣⇒n∣ m n rewrite *-comm m n = m*n∣⇒m∣ n m

*-monoʳ-∣ : ∀ {i j} k → i ∣ j → k * i ∣ k * j
*-monoʳ-∣ {i} {j@.(q * i)} k (divides-refl q) = divides q $ begin-equality
  k * j        ≡⟨⟩
  k * (q * i)  ≡⟨ sym (*-assoc k q i) ⟩
  (k * q) * i  ≡⟨ cong (_* i) (*-comm k q) ⟩
  (q * k) * i  ≡⟨ *-assoc q k i ⟩
  q * (k * i)  ∎
  where open ≤-Reasoning

*-monoˡ-∣ : ∀ {i j} k → i ∣ j → i * k ∣ j * k
*-monoˡ-∣ {i} {j} k rewrite *-comm i k | *-comm j k = *-monoʳ-∣ k

*-cancelˡ-∣ : ∀ {i j} k .{{_ : NonZero k}} → k * i ∣ k * j → i ∣ j
*-cancelˡ-∣ {i} {j} k@(suc _) (divides q eq) =
  divides q $ *-cancelʳ-≡ j (q * i) _ $ begin-equality
    j * k        ≡⟨ *-comm j k ⟩
    k * j        ≡⟨ eq ⟩
    q * (k * i)  ≡⟨ cong (q *_) (*-comm k i) ⟩
    q * (i * k)  ≡⟨ sym (*-assoc q i k) ⟩
    (q * i) * k  ∎
    where open ≤-Reasoning

*-cancelʳ-∣ : ∀ {i j} k .{{_ : NonZero k}} → i * k ∣ j * k → i ∣ j
*-cancelʳ-∣ {i} {j} k rewrite *-comm i k | *-comm j k = *-cancelˡ-∣ k

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

m/n∣m : ∀ {m n} .{{_ : NonZero n}} → n ∣ m → m / n ∣ m
m/n∣m {m@.(p * n)} {n} (divides-refl p) = begin
  m / n     ≡⟨⟩
  p * n / n ≡⟨ m*n/n≡m p n ⟩
  p         ∣⟨ m∣m*n n ⟩
  p * n     ≡⟨⟩
  m         ∎
  where open ∣-Reasoning

m*n∣o⇒m∣o/n : ∀ m n {o} .{{_ : NonZero n}} → m * n ∣ o → m ∣ o / n
m*n∣o⇒m∣o/n m n {o@.(p * (m * n))} (divides-refl p) = begin
  m               ∣⟨ n∣m*n p ⟩
  p * m           ≡⟨ sym (*-identityʳ (p * m)) ⟩
  p * m * 1       ≡⟨ sym (cong (p * m *_) (n/n≡1 n)) ⟩
  p * m * (n / n) ≡⟨ sym (*-/-assoc (p * m) (n∣n {n})) ⟩
  p * m * n / n   ≡⟨ cong (_/ n) (*-assoc p m n) ⟩
  p * (m * n) / n ≡⟨⟩
  o / n           ∎
  where open ∣-Reasoning

m*n∣o⇒n∣o/m : ∀ m n {o} .{{_ : NonZero m}} → m * n ∣ o → n ∣ (o / m)
m*n∣o⇒n∣o/m m n rewrite *-comm m n = m*n∣o⇒m∣o/n n m

m∣n/o⇒m*o∣n : ∀ {m n o} .{{_ : NonZero o}} → o ∣ n → m ∣ n / o → m * o ∣ n
m∣n/o⇒m*o∣n {m} {n} {o} (divides-refl p) m∣p*o/o = begin
  m * o ∣⟨ *-monoˡ-∣ o (subst (m ∣_) (m*n/n≡m p o) m∣p*o/o) ⟩
  p * o ∎
  where open ∣-Reasoning

m∣n/o⇒o*m∣n : ∀ {m n o} .{{_ : NonZero o}} → o ∣ n → m ∣ n / o → o * m ∣ n
m∣n/o⇒o*m∣n {m} {_} {o} rewrite *-comm o m = m∣n/o⇒m*o∣n

m/n∣o⇒m∣o*n : ∀ {m n o} .{{_ : NonZero n}} → n ∣ m → m / n ∣ o → m ∣ o * n
m/n∣o⇒m∣o*n {_} {n} {o} (divides-refl p) p*n/n∣o = begin
  p * n ∣⟨ *-monoˡ-∣ n (subst (_∣ o) (m*n/n≡m p n) p*n/n∣o) ⟩
  o * n ∎
  where open ∣-Reasoning

m∣n*o⇒m/n∣o : ∀ {m n o} .{{_ : NonZero n}} → n ∣ m → m ∣ o * n → m / n ∣ o
m∣n*o⇒m/n∣o {m@.(p * n)} {n@(suc _)} {o} (divides-refl p) pn∣on = begin
  m / n     ≡⟨⟩
  p * n / n ≡⟨ m*n/n≡m p n ⟩
  p         ∣⟨ *-cancelʳ-∣ n pn∣on ⟩
  o         ∎
  where open ∣-Reasoning

------------------------------------------------------------------------
-- Properties of _∣_ and _%_

∣n∣m%n⇒∣m : ∀ {m n d} .{{_ : NonZero n}} → d ∣ n → d ∣ m % n → d ∣ m
∣n∣m%n⇒∣m {m} {n@.(a * d)} {d} (divides-refl a) (divides b m%n≡bd) =
  divides (b + (m / n) * a) (begin-equality
    m                         ≡⟨ m≡m%n+[m/n]*n m n ⟩
    m % n + (m / n) * n       ≡⟨ cong (_+ (m / n) * n) m%n≡bd ⟩
    b * d + (m / n) * n       ≡⟨⟩
    b * d + (m / n) * (a * d) ≡⟨ sym (cong (b * d +_) (*-assoc (m / n) a d)) ⟩
    b * d + ((m / n) * a) * d ≡⟨ sym (*-distribʳ-+ d b _) ⟩
    (b + (m / n) * a) * d     ∎)
    where open ≤-Reasoning

%-presˡ-∣ : ∀ {m n d} .{{_ : NonZero n}} → d ∣ m → d ∣ n → d ∣ m % n
%-presˡ-∣ {m@.(a * d)} {n} {d} (divides-refl a) (divides b 1+n≡bd) =
  divides (a ∸ m / n * b) $ begin-equality
    m % n                   ≡⟨  m%n≡m∸m/n*n m n ⟩
    m ∸ m / n * n           ≡⟨  cong (λ v → m ∸ m / n * v) 1+n≡bd ⟩
    m ∸ m / n * (b * d)     ≡⟨ cong (m ∸_) (*-assoc (m / n) b d) ⟨
    m  ∸ (m / n * b) * d    ≡⟨⟩
    a * d ∸ (m / n * b) * d ≡⟨ *-distribʳ-∸ d a (m / n * b) ⟨
    (a ∸ m / n * b) * d     ∎
  where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of _∣_ and !_

m≤n⇒m!∣n! : ∀ {m n} → m ≤ n → m ! ∣ n !
m≤n⇒m!∣n! m≤n = help (≤⇒≤′ m≤n)
  where
  help : ∀ {m n} → m ≤′ n → m ! ∣ n !
  help {m} {n}     ≤′-refl        = ∣-refl
  help {m} {suc n} (≤′-step m≤′n) = ∣n⇒∣m*n (suc n) (help m≤′n)

------------------------------------------------------------------------
-- Properties of _BoundedNonTrivialDivisor_

-- Smart constructor

hasNonTrivialDivisor-≢ : ∀ {d n} → .{{NonTrivial d}} → .{{NonZero n}} →
                         d ≢ n → d ∣ n → n HasNonTrivialDivisorLessThan n
hasNonTrivialDivisor-≢ d≢n d∣n
  = hasNonTrivialDivisor (≤∧≢⇒< (∣⇒≤ d∣n) d≢n) d∣n

-- Monotonicity wrt ∣

hasNonTrivialDivisor-∣ : ∀ {m n o} → m HasNonTrivialDivisorLessThan n → m ∣ o →
                         o HasNonTrivialDivisorLessThan n
hasNonTrivialDivisor-∣ (hasNonTrivialDivisor d<n d∣m) n∣o
  = hasNonTrivialDivisor d<n (∣-trans d∣m n∣o)

-- Monotonicity wrt ≤

hasNonTrivialDivisor-≤ : ∀ {m n o} → m HasNonTrivialDivisorLessThan n → n ≤ o →
                             m HasNonTrivialDivisorLessThan o
hasNonTrivialDivisor-≤ (hasNonTrivialDivisor d<n d∣m) m≤o =
  hasNonTrivialDivisor (<-≤-trans d<n m≤o) d∣m
