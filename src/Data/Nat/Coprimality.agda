------------------------------------------------------------------------
-- The Agda standard library
--
-- Coprimality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Coprimality where

open import Data.Nat.Base
open import Data.Nat.Divisibility
open import Data.Nat.GCD
open import Data.Nat.GCD.Lemmas
open import Data.Nat.Primality
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Product.Base as Prod
open import Data.Sum.Base as Sum using (inj₁; inj₂)
open import Function.Base using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality.Core as P
  using (_≡_; _≢_; refl; trans; cong; subst)
open import Relation.Nullary as Nullary using (¬_; contradiction; yes ; no)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Symmetric; Decidable)

private
  variable d k m n p : ℕ

open ≤-Reasoning

------------------------------------------------------------------------
-- Definition
--
-- Coprime m n is inhabited iff m and n are coprime (relatively
-- prime), i.e. if their only common divisor is 1.

Coprime : Rel ℕ 0ℓ
Coprime m n = ∀ {d} → d ∣ m × d ∣ n → d ≡ 1

------------------------------------------------------------------------
-- Relationship between GCD and coprimality

coprime⇒GCD≡1 : Coprime m n → GCD m n 1
coprime⇒GCD≡1 {m} {n} coprime = GCD.is (1∣ m , 1∣ n) (∣-reflexive ∘ coprime)

GCD≡1⇒coprime : GCD m n 1 → Coprime m n
GCD≡1⇒coprime g cd with divides q eq ← GCD.greatest g cd
  = m*n≡1⇒n≡1 q _ (P.sym eq)

coprime⇒gcd≡1 : Coprime m n → gcd m n ≡ 1
coprime⇒gcd≡1 coprime = GCD.unique (gcd-GCD _ _) (coprime⇒GCD≡1 coprime)

gcd≡1⇒coprime : gcd m n ≡ 1 → Coprime m n
gcd≡1⇒coprime gcd≡1 = GCD≡1⇒coprime (subst (GCD _ _) gcd≡1 (gcd-GCD _ _))

coprime-/gcd : ∀ m n .{{_ : NonZero (gcd m n)}} →
               Coprime (m / gcd m n) (n / gcd m n)
coprime-/gcd m n = GCD≡1⇒coprime (GCD-/gcd m n)

------------------------------------------------------------------------
-- Relational properties of Coprime

sym : Symmetric Coprime
sym c = c ∘ swap

private
  0≢1 : 0 ≢ 1
  0≢1 ()

  2+≢1 : ∀ {n} → 2+ n ≢ 1
  2+≢1 ()

coprime? : Decidable Coprime
coprime? m n with mkGCD m n
... | (0    , g) = no  (0≢1  ∘ GCD.unique g ∘ coprime⇒GCD≡1)
... | (1    , g) = yes (GCD≡1⇒coprime g)
... | (2+ _ , g) = no  (2+≢1 ∘ GCD.unique g ∘ coprime⇒GCD≡1)

------------------------------------------------------------------------
-- Other basic properties

-- Everything is coprime to 1.

1-coprimeTo : ∀ m → Coprime 1 m
1-coprimeTo m = ∣1⇒≡1 ∘ proj₁

-- Nothing except for 1 is coprime to 0.

0-coprimeTo-m⇒m≡1 : ∀ {m} → Coprime 0 m → m ≡ 1
0-coprimeTo-m⇒m≡1 {m} coprime = coprime (m ∣0 , ∣-refl)

¬0-coprimeTo-2+ : ∀ {n} → ¬ Coprime 0 (2+ n)
¬0-coprimeTo-2+ coprime = contradiction (0-coprimeTo-m⇒m≡1 coprime) λ()

-- If m and n are coprime, then n + m and n are also coprime.

coprime-+ : Coprime m n → Coprime (n + m) n
coprime-+ coprime (d₁ , d₂) = coprime (∣m+n∣m⇒∣n d₁ d₂ , d₂)

-- Recomputable

recompute : .(Coprime n d) → Coprime n d
recompute {n} {d} coprime = Nullary.recompute (coprime? n d) coprime

------------------------------------------------------------------------
-- Relationship with Bezout's lemma

-- If the "gcd" in Bézout's identity is non-zero, then the "other"
-- divisors are coprime.

Bézout-coprime : .{{_ : NonZero d}} →
                 Bézout.Identity d (m * d) (n * d) → Coprime m n
Bézout-coprime {d = suc _} (Bézout.+- x y eq) (divides-refl q₁ , divides-refl q₂) =
  lem₁₀ y q₂ x q₁ eq
Bézout-coprime {d = suc _} (Bézout.-+ x y eq) (divides-refl q₁ , divides-refl q₂) =
  lem₁₀ x q₁ y q₂ eq

-- Coprime numbers satisfy Bézout's identity.

coprime-Bézout : Coprime m n → Bézout.Identity 1 m n
coprime-Bézout = Bézout.identity ∘ coprime⇒GCD≡1

-- If i divides jk and is coprime to j, then it divides k.

coprime-divisor : Coprime m n → m ∣ n * k → m ∣ k
coprime-divisor {k = k} c (divides q eq′) with coprime-Bézout c
... | Bézout.+- x y eq = divides (x * k ∸ y * q) (lem₈ x y eq eq′)
... | Bézout.-+ x y eq = divides (y * q ∸ x * k) (lem₉ x y eq eq′)

-- If d is a common divisor of mk and nk, and m and n are coprime,
-- then d divides k.

coprime-factors : Coprime m n → d ∣ m * k × d ∣ n * k → d ∣ k
coprime-factors c (divides q₁ eq₁ , divides q₂ eq₂) with coprime-Bézout c
... | Bézout.+- x y eq = divides (x * q₁ ∸ y * q₂) (lem₁₁ x y eq eq₁ eq₂)
... | Bézout.-+ x y eq = divides (y * q₂ ∸ x * q₁) (lem₁₁ y x eq eq₂ eq₁)

------------------------------------------------------------------------
-- Primality implies coprimality.

prime⇒coprime≢0 : Prime p → .{{_ : NonZero n}} → n < p → Coprime p n
prime⇒coprime≢0 p n<p (d∣p , d∣n) with prime⇒irreducible p d∣p
... | inj₁ d≡1      = d≡1
... | inj₂ d≡p@refl with () ← ≤⇒≯ (∣⇒≤ d∣n) n<p

prime⇒coprime : ∀ m → Prime m →
                ∀ n → 0 < n → n < m → Coprime m n
prime⇒coprime _ p _ z<s = prime⇒coprime≢0 p

