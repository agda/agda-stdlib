------------------------------------------------------------------------
-- The Agda standard library
--
-- Divisibility
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Divisibility where

open import Data.Nat.Base
open import Data.Nat.DivMod
  using (m≡m%n+[m/n]*n; m%n≡m∸m/n*n; m*n/n≡m; m*n%n≡0; *-/-assoc)
open import Data.Nat.Properties
open import Function.Base using (_∘′_; _$_; flip)
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
import Relation.Binary.Reasoning.Preorder as ≲-Reasoning
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; cong; subst)
open import Relation.Binary.Reasoning.Syntax
open import Relation.Binary.PropositionalEquality.Properties
  using (isEquivalence; module ≡-Reasoning)

private
  variable d m n o p : ℕ


------------------------------------------------------------------------
-- Definition and derived properties

open import Data.Nat.Divisibility.Core public hiding (*-pres-∣)

quotient≢0 : (m∣n : m ∣ n) → .{{NonZero n}} → NonZero (quotient m∣n)
quotient≢0 m∣n rewrite _∣_.equality m∣n = m*n≢0⇒m≢0 (quotient m∣n)

m∣n⇒n≡quotient*m : (m∣n : m ∣ n) → n ≡ (quotient m∣n) * m
m∣n⇒n≡quotient*m m∣n = _∣_.equality m∣n

m∣n⇒n≡m*quotient : (m∣n : m ∣ n) → n ≡ m * (quotient m∣n)
m∣n⇒n≡m*quotient {m = m} m∣n rewrite _∣_.equality m∣n = *-comm (quotient m∣n) m

quotient-∣ : (m∣n : m ∣ n) → (quotient m∣n) ∣ n
quotient-∣ {m = m} m∣n = divides m (m∣n⇒n≡m*quotient m∣n)

quotient>1 : (m∣n : m ∣ n) → m < n → 1 < quotient m∣n
quotient>1 {m} {n} m∣n m<n = *-cancelˡ-< m 1 (quotient m∣n) $ begin-strict
    m * 1        ≡⟨ *-identityʳ m ⟩
    m            <⟨ m<n ⟩
    n            ≡⟨ m∣n⇒n≡m*quotient m∣n ⟩
    m * quotient m∣n ∎
  where open ≤-Reasoning

quotient-< : (m∣n : m ∣ n) → .{{NonTrivial m}} → .{{NonZero n}} → quotient m∣n < n
quotient-< {m} {n} m∣n = begin-strict
  quotient m∣n     <⟨ m<m*n (quotient m∣n) m (nonTrivial⇒n>1 m) ⟩
  quotient m∣n * m ≡⟨ _∣_.equality m∣n ⟨
  n                ∎
  where open ≤-Reasoning; instance _ = quotient≢0 m∣n

------------------------------------------------------------------------
-- Relating _/_ and quotient

n/m≡quotient : (m∣n : m ∣ n) .{{_ : NonZero m}} → n / m ≡ quotient m∣n
n/m≡quotient {m = m} (divides-refl q) = m*n/n≡m q m

------------------------------------------------------------------------
-- Relationship with _%_

m%n≡0⇒n∣m : ∀ m n .{{_ : NonZero n}} → m % n ≡ 0 → n ∣ m
m%n≡0⇒n∣m m n eq = divides (m / n) $ begin
  m                ≡⟨ m≡m%n+[m/n]*n m n ⟩
  m % n + [m/n]*n  ≡⟨ cong (_+ [m/n]*n) eq ⟩
  [m/n]*n          ∎
  where open ≡-Reasoning; [m/n]*n = m / n * n

n∣m⇒m%n≡0 : ∀ m n .{{_ : NonZero n}} → n ∣ m → m % n ≡ 0
n∣m⇒m%n≡0 .(q * n) n (divides-refl q) = m*n%n≡0 q n

m%n≡0⇔n∣m : ∀ m n .{{_ : NonZero n}} → m % n ≡ 0 ⇔ n ∣ m
m%n≡0⇔n∣m m n = mk⇔ (m%n≡0⇒n∣m m n) (n∣m⇒m%n≡0 m n)

------------------------------------------------------------------------
-- Properties of _∣_ and _≤_

∣⇒≤ : .{{_ : NonZero n}} → m ∣ n → m ≤ n
∣⇒≤ {n@.(q * m)} {m} (divides-refl q@(suc p)) = m≤m+n m (p * m)

>⇒∤ : .{{_ : NonZero n}} → m > n → m ∤ n
>⇒∤ {n@(suc _)} n<m@(s<s _) m∣n = contradiction (∣⇒≤ m∣n) (<⇒≱ n<m)

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
∣-antisym {m}     {zero}   _  q∣p = m∣n⇒n≡m*quotient q∣p
∣-antisym {zero}  {n}     p∣q  _  = sym (m∣n⇒n≡m*quotient p∣q)
∣-antisym {suc m} {suc n} p∣q q∣p = ≤-antisym (∣⇒≤ p∣q) (∣⇒≤ q∣p)

infix 4 _∣?_

_∣?_ : Decidable _∣_
zero  ∣? zero   = yes (divides-refl 0)
zero  ∣? suc m  = no ((λ()) ∘′ ∣-antisym (divides-refl 0))
n@(suc _) ∣? m  = Dec.map (m%n≡0⇔n∣m m n) (m % n ≟ 0)

∣-isPreorder : IsPreorder _≡_ _∣_
∣-isPreorder = record
  { isEquivalence = isEquivalence
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
  private module Base = ≲-Reasoning ∣-preorder

  open Base public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨; step-∼; step-≲)
    renaming (≲-go to ∣-go)

  open ∣-syntax _IsRelatedTo_ _IsRelatedTo_ ∣-go public


------------------------------------------------------------------------
-- Simple properties of _∣_

infix 10 _∣0 1∣_

_∣0 : ∀ n → n ∣ 0
n ∣0 = divides-refl 0

0∣⇒≡0 : 0 ∣ n → n ≡ 0
0∣⇒≡0 {n} 0∣n = ∣-antisym (n ∣0) 0∣n

1∣_ : ∀ n → 1 ∣ n
1∣ n = divides n (sym (*-identityʳ n))

∣1⇒≡1 : n ∣ 1 → n ≡ 1
∣1⇒≡1 {n} n∣1 = ∣-antisym n∣1 (1∣ n)

n∣n : n ∣ n
n∣n = ∣-refl

------------------------------------------------------------------------
-- Properties of _∣_ and _+_

∣m∣n⇒∣m+n : d ∣ m → d ∣ n → d ∣ m + n
∣m∣n⇒∣m+n (divides-refl p) (divides-refl q) =
  divides (p + q) (sym (*-distribʳ-+ _ p q))

∣m+n∣m⇒∣n : d ∣ m + n → d ∣ m → d ∣ n
∣m+n∣m⇒∣n {d} {m} {n} (divides p m+n≡p*d) (divides-refl q) =
  divides (p ∸ q) $ begin-equality
    n             ≡⟨ m+n∸n≡m n m ⟨
    n + m ∸ m     ≡⟨ cong (_∸ m) (+-comm n m) ⟩
    m + n ∸ m     ≡⟨ cong (_∸ m) m+n≡p*d ⟩
    p * d ∸ q * d ≡⟨ *-distribʳ-∸ d p q ⟨
    (p ∸ q) * d   ∎
    where open ∣-Reasoning

------------------------------------------------------------------------
-- Properties of _∣_ and _*_

n∣m*n : ∀ m {n} → n ∣ m * n
n∣m*n m = divides m refl

m∣m*n : ∀ {m} n → m ∣ m * n
m∣m*n n = divides n (*-comm _ n)

n∣m*n*o : ∀ m {n} o → n ∣ m * n * o
n∣m*n*o m o = ∣-trans (n∣m*n m) (m∣m*n o)

∣m⇒∣m*n : ∀ n → d ∣ m → d ∣ m * n
∣m⇒∣m*n n (divides-refl q) = ∣-trans (n∣m*n q) (m∣m*n n)

∣n⇒∣m*n : ∀ m {n} → d ∣ n → d ∣ m * n
∣n⇒∣m*n m {n} rewrite *-comm m n = ∣m⇒∣m*n m

m*n∣⇒m∣ : ∀ m n → m * n ∣ d → m ∣ d
m*n∣⇒m∣ m n (divides-refl q) = ∣n⇒∣m*n q (m∣m*n n)

m*n∣⇒n∣ : ∀ m n → m * n ∣ d → n ∣ d
m*n∣⇒n∣ m n rewrite *-comm m n = m*n∣⇒m∣ n m

*-pres-∣ : o ∣ m → p ∣ n → o * p ∣ m * n
*-pres-∣ {o} {m@.(q * o)} {p} {n@.(r * p)} (divides-refl q) (divides-refl r) =
  divides (q * r) ([m*n]*[o*p]≡[m*o]*[n*p] q o r p)

*-monoʳ-∣ : ∀ o → m ∣ n → o * m ∣ o * n
*-monoʳ-∣ o = *-pres-∣ (∣-refl {o})

*-monoˡ-∣ : ∀ o → m ∣ n → m * o ∣ n * o
*-monoˡ-∣ o = flip *-pres-∣ (∣-refl {o})

*-cancelˡ-∣ : ∀ o .{{_ : NonZero o}} → o * m ∣ o * n → m ∣ n
*-cancelˡ-∣ {m} {n} o o*m∣o*n = divides q $ *-cancelˡ-≡ n (q * m) o $ begin-equality
  o * n       ≡⟨ m∣n⇒n≡m*quotient o*m∣o*n ⟩
  o * m * q   ≡⟨ *-assoc o m q ⟩
  o * (m * q) ≡⟨ cong (o *_) (*-comm q m) ⟨
  o * (q * m) ∎
  where
  open ∣-Reasoning
  q = quotient o*m∣o*n

*-cancelʳ-∣ : ∀ o .{{_ : NonZero o}} → m * o ∣ n * o → m ∣ n
*-cancelʳ-∣ {m} {n} o rewrite *-comm m o | *-comm n o = *-cancelˡ-∣ o

------------------------------------------------------------------------
-- Properties of _∣_ and _∸_

∣m∸n∣n⇒∣m : ∀ d → n ≤ m → d ∣ m ∸ n → d ∣ n → d ∣ m
∣m∸n∣n⇒∣m {n} {m} d n≤m (divides p m∸n≡p*d) (divides-refl q) =
  divides (p + q) $ begin-equality
    m             ≡⟨ m+[n∸m]≡n n≤m ⟨
    n + (m ∸ n)   ≡⟨ +-comm n (m ∸ n) ⟩
    m ∸ n + n     ≡⟨ cong (_+ n) m∸n≡p*d ⟩
    p * d + q * d ≡⟨ *-distribʳ-+ d p q ⟨
    (p + q) * d   ∎
  where open ∣-Reasoning

------------------------------------------------------------------------
-- Properties of _∣_ and _/_

m/n∣m : .{{_ : NonZero n}} → n ∣ m → m / n ∣ m
m/n∣m {n} {m} n∣m = begin
  m / n        ≡⟨ n/m≡quotient n∣m ⟩
  quotient n∣m ∣⟨ quotient-∣ n∣m ⟩
  m            ∎
  where open ∣-Reasoning

m*n∣o⇒m∣o/n : ∀ m n .{{_ : NonZero n}} → m * n ∣ o → m ∣ o / n
m*n∣o⇒m∣o/n m n (divides-refl p) = divides p $ begin-equality
  p * (m * n) / n   ≡⟨ *-/-assoc p (n∣m*n m) ⟩
  p * ((m * n) / n) ≡⟨ cong (p *_) (m*n/n≡m m n) ⟩
  p * m ∎
  where open ∣-Reasoning

m*n∣o⇒n∣o/m : ∀ m n .{{_ : NonZero m}} → m * n ∣ o → n ∣ (o / m)
m*n∣o⇒n∣o/m m n rewrite *-comm m n = m*n∣o⇒m∣o/n n m

m∣n/o⇒m*o∣n : .{{_ : NonZero o}} → o ∣ n → m ∣ n / o → m * o ∣ n
m∣n/o⇒m*o∣n {o} {n@.(p * o)} {m} (divides-refl p) m∣p*o/o = begin
  m * o ∣⟨ *-monoˡ-∣ o (subst (m ∣_) (m*n/n≡m p o) m∣p*o/o) ⟩
  p * o ∎
  where open ∣-Reasoning

m∣n/o⇒o*m∣n : .{{_ : NonZero o}} → o ∣ n → m ∣ n / o → o * m ∣ n
m∣n/o⇒o*m∣n {o} {_} {m} rewrite *-comm o m = m∣n/o⇒m*o∣n

m/n∣o⇒m∣o*n : .{{_ : NonZero n}} → n ∣ m → m / n ∣ o → m ∣ o * n
m/n∣o⇒m∣o*n {n} {m@.(p * n)} {o} (divides-refl p) p*n/n∣o = begin
  p * n ∣⟨ *-monoˡ-∣ n (subst (_∣ o) (m*n/n≡m p n) p*n/n∣o) ⟩
  o * n ∎
  where open ∣-Reasoning

m∣n*o⇒m/n∣o : .{{_ : NonZero n}} → n ∣ m → m ∣ o * n → m / n ∣ o
m∣n*o⇒m/n∣o {n} {m@.(p * n)} {o} (divides-refl p) pn∣on = begin
  m / n     ≡⟨⟩
  p * n / n ≡⟨ m*n/n≡m p n ⟩
  p         ∣⟨ *-cancelʳ-∣ n pn∣on ⟩
  o         ∎
  where open ∣-Reasoning

------------------------------------------------------------------------
-- Properties of _∣_ and _%_

∣n∣m%n⇒∣m : .{{_ : NonZero n}} → d ∣ n → d ∣ m % n → d ∣ m
∣n∣m%n⇒∣m {n@.(p * d)} {d} {m} (divides-refl p) (divides q m%n≡qd) =
  divides (q + (m / n) * p) $ begin-equality
    m                         ≡⟨ m≡m%n+[m/n]*n m n ⟩
    m % n + (m / n) * n       ≡⟨ cong (_+ (m / n) * n) m%n≡qd ⟩
    q * d + (m / n) * n       ≡⟨⟩
    q * d + (m / n) * (p * d) ≡⟨ cong (q * d +_) (*-assoc (m / n) p d) ⟨
    q * d + ((m / n) * p) * d ≡⟨ *-distribʳ-+ d q _ ⟨
    (q + (m / n) * p) * d     ∎
  where open ∣-Reasoning

%-presˡ-∣ : .{{_ : NonZero n}} → d ∣ m → d ∣ n → d ∣ m % n
%-presˡ-∣ {n} {d} {m@.(p * d)} (divides-refl p) (divides q 1+n≡qd) =
  divides (p ∸ m / n * q) $ begin-equality
    m % n                   ≡⟨ m%n≡m∸m/n*n m n ⟩
    m ∸ m / n * n           ≡⟨ cong (λ v → m ∸ m / n * v) 1+n≡qd ⟩
    m ∸ m / n * (q * d)     ≡⟨ cong (m ∸_) (*-assoc (m / n) q d) ⟨
    m  ∸ (m / n * q) * d    ≡⟨⟩
    p * d ∸ (m / n * q) * d ≡⟨ *-distribʳ-∸ d p (m / n * q) ⟨
    (p ∸ m / n * q) * d     ∎
  where open ∣-Reasoning

------------------------------------------------------------------------
-- Properties of _∣_ and !_

m≤n⇒m!∣n! : m ≤ n → m ! ∣ n !
m≤n⇒m!∣n! m≤n = help (≤⇒≤′ m≤n)
  where
  help : m ≤′ n → m ! ∣ n !
  help         ≤′-refl       = ∣-refl
  help {n = n} (≤′-step m≤n) = ∣n⇒∣m*n n (help m≤n)

------------------------------------------------------------------------
-- Properties of _HasNonTrivialDivisorLessThan_

-- Smart constructor

hasNonTrivialDivisor-≢ : .{{NonTrivial d}} → .{{NonZero n}} →
                         d ≢ n → d ∣ n → n HasNonTrivialDivisorLessThan n
hasNonTrivialDivisor-≢ d≢n d∣n
  = hasNonTrivialDivisor (≤∧≢⇒< (∣⇒≤ d∣n) d≢n) d∣n

-- Monotonicity wrt ∣

hasNonTrivialDivisor-∣ : m HasNonTrivialDivisorLessThan n → m ∣ o →
                         o HasNonTrivialDivisorLessThan n
hasNonTrivialDivisor-∣ (hasNonTrivialDivisor d<n d∣m) m∣o
  = hasNonTrivialDivisor d<n (∣-trans d∣m m∣o)

-- Monotonicity wrt ≤

hasNonTrivialDivisor-≤ : m HasNonTrivialDivisorLessThan n → n ≤ o →
                         m HasNonTrivialDivisorLessThan o
hasNonTrivialDivisor-≤ (hasNonTrivialDivisor d<n d∣m) n≤o
  = hasNonTrivialDivisor (<-≤-trans d<n n≤o) d∣m
