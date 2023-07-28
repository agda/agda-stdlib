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
open import Data.Unit.Base using (tt)
open import Function.Base using (_∘′_; _$_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (0ℓ)
open import Relation.Nullary.Decidable as Dec using (False; yes; no)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Binary
import Relation.Binary.Reasoning.Preorder as PreorderReasoning
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
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
n∣m⇒m%n≡0 m n (divides v eq) = begin-equality
  m       % n  ≡⟨ cong (_% n) eq ⟩
  (v * n) % n  ≡⟨ m*n%n≡0 v n ⟩
  0            ∎
  where open ≤-Reasoning

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
  private
    module Base = PreorderReasoning ∣-preorder

  open Base public
    hiding (step-≈; step-≈˘; step-∼)

  infixr 2 step-∣
  step-∣ = Base.step-∼
  syntax step-∣ x y∣z x∣y = x ∣⟨ x∣y ⟩ y∣z

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

n∣m*n*o : ∀ m {n} o → n ∣ m * n * o
n∣m*n*o m o = ∣-trans (n∣m*n m) (m∣m*n o)

∣m⇒∣m*n : ∀ {i m} n → i ∣ m → i ∣ m * n
∣m⇒∣m*n {i} {m} n (divides q refl) = ∣-trans (n∣m*n q) (m∣m*n n)

∣n⇒∣m*n : ∀ {i} m {n} → i ∣ n → i ∣ m * n
∣n⇒∣m*n m {n} rewrite *-comm m n = ∣m⇒∣m*n m

m*n∣⇒m∣ : ∀ {i} m n → m * n ∣ i → m ∣ i
m*n∣⇒m∣ m n (divides q refl) = ∣n⇒∣m*n q (m∣m*n n)

m*n∣⇒n∣ : ∀ {i} m n → m * n ∣ i → n ∣ i
m*n∣⇒n∣ m n rewrite *-comm m n = m*n∣⇒m∣ n m

*-monoʳ-∣ : ∀ {i j} k → i ∣ j → k * i ∣ k * j
*-monoʳ-∣ {i} {j} k (divides q refl) = divides q $ begin-equality
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
m/n∣m {m} {n} (divides p refl) = begin
  p * n / n ≡⟨ m*n/n≡m p n ⟩
  p         ∣⟨ m∣m*n n ⟩
  p * n     ∎
  where open ∣-Reasoning

m*n∣o⇒m∣o/n : ∀ m n {o} .{{_ : NonZero n}} → m * n ∣ o → m ∣ o / n
m*n∣o⇒m∣o/n m n {_} (divides p refl) = begin
  m               ∣⟨ n∣m*n p ⟩
  p * m           ≡⟨ sym (*-identityʳ (p * m)) ⟩
  p * m * 1       ≡⟨ sym (cong (p * m *_) (n/n≡1 n)) ⟩
  p * m * (n / n) ≡⟨ sym (*-/-assoc (p * m) (n∣n {n})) ⟩
  p * m * n / n   ≡⟨ cong (_/ n) (*-assoc p m n) ⟩
  p * (m * n) / n ∎
  where open ∣-Reasoning

m*n∣o⇒n∣o/m : ∀ m n {o} .{{_ : NonZero m}} → m * n ∣ o → n ∣ (o / m)
m*n∣o⇒n∣o/m m n rewrite *-comm m n = m*n∣o⇒m∣o/n n m

m∣n/o⇒m*o∣n : ∀ {m n o} .{{_ : NonZero o}} → o ∣ n → m ∣ n / o → m * o ∣ n
m∣n/o⇒m*o∣n {m} {n} {o} (divides p refl) m∣p*o/o = begin
  m * o ∣⟨ *-monoˡ-∣ o (subst (m ∣_) (m*n/n≡m p o) m∣p*o/o) ⟩
  p * o ∎
  where open ∣-Reasoning

m∣n/o⇒o*m∣n : ∀ {m n o} .{{_ : NonZero o}} → o ∣ n → m ∣ n / o → o * m ∣ n
m∣n/o⇒o*m∣n {m} {_} {o} rewrite *-comm o m = m∣n/o⇒m*o∣n

m/n∣o⇒m∣o*n : ∀ {m n o} .{{_ : NonZero n}} → n ∣ m → m / n ∣ o → m ∣ o * n
m/n∣o⇒m∣o*n {_} {n} {o} (divides p refl) p*n/n∣o = begin
  p * n ∣⟨ *-monoˡ-∣ n (subst (_∣ o) (m*n/n≡m p n) p*n/n∣o) ⟩
  o * n ∎
  where open ∣-Reasoning

m∣n*o⇒m/n∣o : ∀ {m n o} .{{_ : NonZero n}} → n ∣ m → m ∣ o * n → m / n ∣ o
m∣n*o⇒m/n∣o {_} {n@(suc _)} {o} (divides p refl) pn∣on = begin
  p * n / n ≡⟨ m*n/n≡m p n ⟩
  p         ∣⟨ *-cancelʳ-∣ n pn∣on ⟩
  o         ∎
  where open ∣-Reasoning

------------------------------------------------------------------------
-- Properties of _∣_ and _%_

∣n∣m%n⇒∣m : ∀ {m n d} .{{_ : NonZero n}} → d ∣ n → d ∣ m % n → d ∣ m
∣n∣m%n⇒∣m {m} {n} {d} (divides a n≡ad) (divides b m%n≡bd) =
  divides (b + (m / n) * a) (begin-equality
    m                         ≡⟨ m≡m%n+[m/n]*n m n ⟩
    m % n + (m / n) * n       ≡⟨ cong₂ _+_ m%n≡bd (cong (m / n *_) n≡ad) ⟩
    b * d + (m / n) * (a * d) ≡⟨ sym (cong (b * d +_) (*-assoc (m / n) a d)) ⟩
    b * d + ((m / n) * a) * d ≡⟨ sym (*-distribʳ-+ d b _) ⟩
    (b + (m / n) * a) * d     ∎)
    where open ≤-Reasoning

%-presˡ-∣ : ∀ {m n d} .{{_ : NonZero n}} → d ∣ m → d ∣ n → d ∣ m % n
%-presˡ-∣ {m} {n} {d} (divides a refl) (divides b 1+n≡bd) =
  divides (a ∸ ad/n * b) $ begin-equality
    a * d % n              ≡⟨  m%n≡m∸m/n*n (a * d) n ⟩
    a * d ∸ ad/n * n       ≡⟨  cong (λ v → a * d ∸ ad/n * v) 1+n≡bd ⟩
    a * d ∸ ad/n * (b * d) ≡˘⟨ cong (a * d ∸_) (*-assoc ad/n b d) ⟩
    a * d ∸ (ad/n * b) * d ≡˘⟨ *-distribʳ-∸ d a (ad/n * b) ⟩
    (a ∸ ad/n * b) * d     ∎
  where open ≤-Reasoning; ad/n = a * d / n

------------------------------------------------------------------------
-- Properties of _∣_ and !_

m≤n⇒m!∣n! : ∀ {m n} → m ≤ n → m ! ∣ n !
m≤n⇒m!∣n! m≤n = help (≤⇒≤′ m≤n)
  where
  help : ∀ {m n} → m ≤′ n → m ! ∣ n !
  help {m} {n}     ≤′-refl        = ∣-refl
  help {m} {suc n} (≤′-step m≤′n) = ∣n⇒∣m*n (suc n) (help m≤′n)
