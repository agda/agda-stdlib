------------------------------------------------------------------------
-- The Agda standard library
--
-- Divisibility
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Divisibility where

open import Data.Nat.Base
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Function.Base using (_∘′_; _$_; flip)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (0ℓ)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.Bundles using (Preorder; Poset)
open import Relation.Binary.Structures
  using (IsPreorder; IsPartialOrder)
open import Relation.Binary.Definitions
  using (Reflexive; Transitive; Antisymmetric; Decidable)
import Relation.Binary.Reasoning.Preorder as PreorderReasoning
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; cong; cong₂; subst)
open import Relation.Binary.Reasoning.Syntax
open import Relation.Binary.PropositionalEquality.Properties
  using (isEquivalence; module ≡-Reasoning)

private
  variable d m n o : ℕ


------------------------------------------------------------------------
-- Definition and derived properties

open import Data.Nat.Divisibility.Core public

module _ (m∣n : m ∣ n) where

  open _∣_ m∣n renaming (quotient to q)
  open ≤-Reasoning

  instance
    quotient≢0 : .⦃ NonZero n ⦄ → NonZero q
    quotient≢0 rewrite equality = m*n≢0⇒m≢0 q

  quotient∣ : q ∣ n
  quotient∣ = divides m equalityᵒ

  quotient>1 : m < n → 1 < q
  quotient>1 m<n = *-cancelˡ-< m 1 q $ begin-strict
      m * 1 ≡⟨ *-identityʳ m ⟩
      m     <⟨ m<n ⟩
      n     ≡⟨ equalityᵒ ⟩
      m * q ∎

  quotient< : 1 < m → .⦃ NonZero n ⦄ → q < n
  quotient< 1<m = begin-strict
    q     <⟨ m<m*n q m 1<m ⟩
    q * m ≡⟨ equality ⟨
    n     ∎


------------------------------------------------------------------------
-- Relationship with _%_

m%n≡0⇒n∣m : ∀ m n .⦃ _ : NonZero n ⦄ → m % n ≡ 0 → n ∣ m
m%n≡0⇒n∣m m n eq = divides (m / n) $ begin
  m                  ≡⟨ m≡m%n+[m/n]*n m n ⟩
  m % n + m / n * n  ≡⟨ cong₂ (_+_) eq refl ⟩
  m / n * n          ∎
  where open ≡-Reasoning

n∣m⇒m%n≡0 : ∀ m n .⦃ _ : NonZero n ⦄ → n ∣ m → m % n ≡ 0
n∣m⇒m%n≡0 .(q * n) n (divides-refl q) = m*n%n≡0 q n

m%n≡0⇔n∣m : ∀ m n .⦃ _ : NonZero n ⦄ → m % n ≡ 0 ⇔ n ∣ m
m%n≡0⇔n∣m m n = mk⇔ (m%n≡0⇒n∣m m n) (n∣m⇒m%n≡0 m n)

------------------------------------------------------------------------
-- Properties of _∣_ and _≤_

∣⇒≤ : .⦃ _ : NonZero n ⦄ → m ∣ n → m ≤ n
∣⇒≤ {n@(suc _)} {m} (divides q@(suc p) eq) = begin
  m      ≤⟨ m≤m+n m (p * m) ⟩
  q * m  ≡⟨ eq ⟨
  n      ∎
  where open ≤-Reasoning

>⇒∤ : .⦃ _ : NonZero n ⦄ → m > n → m ∤ n
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
∣-antisym {m}     {zero}   _  q∣p = equalityᵒ where open _∣_ q∣p
∣-antisym {zero}  {n}     p∣q  _  = sym equalityᵒ where open _∣_ p∣q
∣-antisym {suc m} {suc n} p∣q q∣p = ≤-antisym (∣⇒≤ p∣q) (∣⇒≤ q∣p)

infix 4 _∣?_

_∣?_ : Decidable _∣_
zero  ∣? zero   = Dec.yes (divides-refl 0)
zero  ∣? suc m  = Dec.no ((λ()) ∘′ ∣-antisym (divides-refl 0))
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
  private module Base = PreorderReasoning ∣-preorder

  open Base public
    hiding (step-≈; step-≈˘; step-≈-⟩; step-≈-⟨; step-∼; step-≲)
    renaming (≲-go to ∣-go)

  open ∣-syntax _IsRelatedTo_ _IsRelatedTo_ ∣-go public

open ∣-Reasoning

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
n∣n {n} = ∣-refl

------------------------------------------------------------------------
-- Properties of _∣_ and _+_

∣m∣n⇒∣m+n : d ∣ m → d ∣ n → d ∣ m + n
∣m∣n⇒∣m+n (divides-refl p) (divides-refl q) =
  divides (p + q) (sym (*-distribʳ-+ _ p q))

∣m+n∣m⇒∣n : d ∣ m + n → d ∣ m → d ∣ n
∣m+n∣m⇒∣n {d} {m} {n} (divides p m+n≡p*d) (divides q m≡q*d) =
  divides (p ∸ q) $ begin-equality
    n             ≡⟨ m+n∸n≡m n m ⟨
    n + m ∸ m     ≡⟨ cong (_∸ m) (+-comm n m) ⟩
    m + n ∸ m     ≡⟨ cong₂ _∸_ m+n≡p*d m≡q*d ⟩
    p * d ∸ q * d ≡⟨ *-distribʳ-∸ d p q ⟨
    (p ∸ q) * d   ∎

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

*-monoʳ-∣ : ∀ k → m ∣ n → k * m ∣ k * n
*-monoʳ-∣ k = *-pres-∣ (∣-refl {k})

*-monoˡ-∣ : ∀ k → m ∣ n → m * k ∣ n * k
*-monoˡ-∣ k = flip *-pres-∣ (∣-refl {k})

*-cancelˡ-∣ : ∀ k .⦃ _ : NonZero k ⦄ → k * m ∣ k * n → m ∣ n
*-cancelˡ-∣ {m} {n} k k*m∣k*n = divides q $ *-cancelˡ-≡ n (q * m) k $ begin-equality
  k * n       ≡⟨ equalityᵒ ⟩
  k * m * q   ≡⟨ *-assoc k m q ⟩
  k * (m * q) ≡⟨ cong (k *_) (*-comm q m) ⟨
  k * (q * m) ∎
  where open _∣_ k*m∣k*n renaming (quotient to q)

*-cancelʳ-∣ : ∀ k .⦃ _ : NonZero k ⦄ → m * k ∣ n * k → m ∣ n
*-cancelʳ-∣ {m} {n} k rewrite *-comm m k | *-comm n k = *-cancelˡ-∣ k

------------------------------------------------------------------------
-- Properties of _∣_ and _∸_

∣m∸n∣n⇒∣m : ∀ d → n ≤ m → d ∣ m ∸ n → d ∣ n → d ∣ m
∣m∸n∣n⇒∣m {n} {m} d n≤m (divides p m∸n≡p*d) (divides q n≡q*o) =
  divides (p + q) $ begin-equality
    m             ≡⟨ m+[n∸m]≡n n≤m ⟨
    n + (m ∸ n)   ≡⟨ +-comm n (m ∸ n) ⟩
    m ∸ n + n     ≡⟨ cong₂ _+_ m∸n≡p*d n≡q*o ⟩
    p * d + q * d ≡⟨ *-distribʳ-+ d p q ⟨
    (p + q) * d   ∎

------------------------------------------------------------------------
-- Properties of _∣_ and _/_

m/n∣m : .⦃ _ : NonZero n ⦄ → n ∣ m → m / n ∣ m
m/n∣m {n} {m@.(p * n)} (divides-refl p) = begin
  m / n     ≡⟨⟩
  p * n / n ≡⟨ m*n/n≡m p n ⟩
  p         ∣⟨ m∣m*n n ⟩
  p * n     ≡⟨⟩
  m         ∎

m*n∣o⇒m∣o/n : ∀ m n .⦃ _ : NonZero n ⦄ → m * n ∣ o → m ∣ o / n
m*n∣o⇒m∣o/n m n (divides-refl p) = divides p $ begin-equality
  p * (m * n) / n   ≡⟨ *-/-assoc p (n∣m*n m) ⟩
  p * ((m * n) / n) ≡⟨ cong (p *_) (m*n/n≡m m n) ⟩
  p * m ∎

m*n∣o⇒n∣o/m : ∀ m n .⦃ _ : NonZero m ⦄ → m * n ∣ o → n ∣ (o / m)
m*n∣o⇒n∣o/m m n rewrite *-comm m n = m*n∣o⇒m∣o/n n m

m∣n/o⇒m*o∣n : .⦃ _ : NonZero o ⦄ → o ∣ n → m ∣ n / o → m * o ∣ n
m∣n/o⇒m*o∣n {o} {n} {m} (divides-refl p) m∣p*o/o = begin
  m * o ∣⟨ *-monoˡ-∣ o (subst (m ∣_) (m*n/n≡m p o) m∣p*o/o) ⟩
  p * o ∎

m∣n/o⇒o*m∣n : .⦃ _ : NonZero o ⦄ → o ∣ n → m ∣ n / o → o * m ∣ n
m∣n/o⇒o*m∣n {o} {_} {m} rewrite *-comm o m = m∣n/o⇒m*o∣n

m/n∣o⇒m∣o*n : .⦃ _ : NonZero n ⦄ → n ∣ m → m / n ∣ o → m ∣ o * n
m/n∣o⇒m∣o*n {n} {o = o} (divides-refl p) p*n/n∣o = begin
  p * n ∣⟨ *-monoˡ-∣ n (subst (_∣ o) (m*n/n≡m p n) p*n/n∣o) ⟩
  o * n ∎

m∣n*o⇒m/n∣o : .⦃ _ : NonZero n ⦄ → n ∣ m → m ∣ o * n → m / n ∣ o
m∣n*o⇒m/n∣o {n} {m@.(p * n)} {o} (divides-refl p) pn∣on = begin
  m / n     ≡⟨⟩
  p * n / n ≡⟨ m*n/n≡m p n ⟩
  p         ∣⟨ *-cancelʳ-∣ n pn∣on ⟩
  o         ∎

------------------------------------------------------------------------
-- Properties of _∣_ and _%_

∣n∣m%n⇒∣m : .⦃ _ : NonZero n ⦄ → d ∣ n → d ∣ m % n → d ∣ m
∣n∣m%n⇒∣m {n@.(p * d)} {d} {m} (divides-refl p) (divides q m%n≡qd) =
  divides (q + (m / n) * p) $ begin-equality
    m                         ≡⟨ m≡m%n+[m/n]*n m n ⟩
    m % n + (m / n) * n       ≡⟨ cong (_+ (m / n) * n) m%n≡qd ⟩
    q * d + (m / n) * n       ≡⟨⟩
    q * d + (m / n) * (p * d) ≡⟨ cong (q * d +_) (*-assoc (m / n) p d) ⟨
    q * d + ((m / n) * p) * d ≡⟨ *-distribʳ-+ d q _ ⟨
    (q + (m / n) * p) * d     ∎

%-presˡ-∣ : .⦃ _ : NonZero n ⦄ → d ∣ m → d ∣ n → d ∣ m % n
%-presˡ-∣ {n} {d} {m@.(p * d)} (divides-refl p) (divides q 1+n≡qd) =
  divides (p ∸ m / n * q) $ begin-equality
    m % n                   ≡⟨ m%n≡m∸m/n*n m n ⟩
    m ∸ m / n * n           ≡⟨ cong (λ v → m ∸ m / n * v) 1+n≡qd ⟩
    m ∸ m / n * (q * d)     ≡⟨ cong (m ∸_) (*-assoc (m / n) q d) ⟨
    m  ∸ (m / n * q) * d    ≡⟨⟩
    p * d ∸ (m / n * q) * d ≡⟨ *-distribʳ-∸ d p (m / n * q) ⟨
    (p ∸ m / n * q) * d     ∎

------------------------------------------------------------------------
-- Properties of _∣_ and !_

m≤n⇒m!∣n! : m ≤ n → m ! ∣ n !
m≤n⇒m!∣n! m≤n = help (≤⇒≤′ m≤n)
  where
  help : m ≤′ n → m ! ∣ n !
  help         ≤′-refl       = ∣-refl
  help {n = n} (≤′-step m≤n) = ∣n⇒∣m*n n (help m≤n)
